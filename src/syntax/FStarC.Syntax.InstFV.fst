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
module FStarC.Syntax.InstFV
open FStarC.Effect
open FStarC.Syntax.Syntax
open FStarC.Ident
open FStarC.Util
open FStarC

module S = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module U = FStarC.Util

let mk t s = S.mk s t.pos

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

      | Tm_abs {bs; body; rc_opt=lopt} ->
        let bs = inst_binders s bs in
        let body = inst s body in
        mk (Tm_abs {bs; body; rc_opt=inst_lcomp_opt s lopt})

      | Tm_arrow {bs; comp=c} ->
        let bs = inst_binders s bs in
        let c = inst_comp s c in
        mk (Tm_arrow {bs; comp=c})

      | Tm_refine {b=bv; phi=t} ->
        let bv = {bv with sort=inst s bv.sort} in
        let t = inst s t in
        mk (Tm_refine {b=bv; phi=t})

      | Tm_app {hd=t; args} ->
        mk (Tm_app {hd=inst s t; args=inst_args s args})

      | Tm_match {scrutinee=t; ret_opt=asc_opt; brs=pats; rc_opt=lopt} ->
        let pats = pats |> List.map (fun (p, wopt, t) ->
            let wopt = match wopt with
                | None ->   None
                | Some w -> Some (inst s w) in
            let t = inst s t in
            (p, wopt, t)) in
        let asc_opt =
          match asc_opt with
          | None -> None
          | Some (b, asc) ->
            Some (inst_binder s b, inst_ascription s asc) in
        mk (Tm_match {scrutinee=inst s t;
                      ret_opt=asc_opt;
                      brs=pats;
                      rc_opt=inst_lcomp_opt s lopt})

      | Tm_ascribed {tm=t1; asc; eff_opt=f} ->
        mk (Tm_ascribed {tm=inst s t1; asc=inst_ascription s asc; eff_opt=f})

      | Tm_let {lbs; body=t} ->
        let lbs = fst lbs, snd lbs |> List.map (fun lb -> {lb with lbtyp=inst s lb.lbtyp; lbdef=inst s lb.lbdef}) in
        mk (Tm_let {lbs; body=inst s t})

      | Tm_meta {tm=t; meta=Meta_pattern (bvs, args)} ->
        mk (Tm_meta {tm=inst s t; meta=Meta_pattern (bvs, args |> List.map (inst_args s))})

      | Tm_meta {tm=t; meta=Meta_monadic (m, t')} ->
        mk (Tm_meta {tm=inst s t; meta=Meta_monadic(m, inst s t')})

      | Tm_meta {tm=t; meta=tag} ->
        mk (Tm_meta {tm=inst s t; meta=tag})

and inst_binder s b =
  { b with
    binder_bv = { b.binder_bv with sort = inst s b.binder_bv.sort };
    binder_attrs = b.binder_attrs |> List.map (inst s) }

and inst_binders s bs = bs |> List.map (inst_binder s)

and inst_args s args = args |> List.map (fun (a, imp) -> inst s a, imp)

and inst_comp s c = match c.n with
    | Total t -> S.mk_Total (inst s t)
    | GTotal t -> S.mk_GTotal (inst s t)
    | Comp ct -> let ct = {ct with result_typ=inst s ct.result_typ;
                                   effect_args=inst_args s ct.effect_args;
                                   flags=ct.flags |> List.map (function
                                        | DECREASES dec_order ->
                                          DECREASES (inst_decreases_order s dec_order)
                                        | f -> f)} in
                 S.mk_Comp ct

and inst_decreases_order s = function
    | Decreases_lex l -> Decreases_lex (l |> List.map (inst s))
    | Decreases_wf (rel, e) -> Decreases_wf (inst s rel, inst s e)

and inst_lcomp_opt s l = match l with
    | None -> None
    | Some rc -> Some ({rc with residual_typ = FStarC.Util.map_opt rc.residual_typ (inst s)})

and inst_ascription s (asc:ascription) =
  let annot, topt, use_eq = asc in
  let annot =
    match annot with
    | Inl t -> Inl (inst s t)
    | Inr c -> Inr (inst_comp s c) in
  let topt = FStarC.Util.map_opt topt (inst s) in
  annot, topt, use_eq

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
