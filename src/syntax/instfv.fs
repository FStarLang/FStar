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
open FStar.Syntax.Syntax
open FStar.Ident
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U = FStar.Util
type inst_t = list<(lident * universes)>

// VALS_HACK_HERE

let rec inst (s:inst_t) t = 
    let t = SS.compress t in
    let mk s = S.mk s !t.tk t.pos in
    match t.n with
      | Tm_delayed _ -> failwith "Impossible"

      | Tm_name _ 
      | Tm_uvar _
      | Tm_uvar _
      | Tm_type _
      | Tm_bvar _
      | Tm_constant _
      | Tm_unknown 
      | Tm_uinst _ -> t

      | Tm_fvar fv -> 
        begin match U.find_opt (fun (x, _) -> lid_equals x (fst fv).v) s with 
            | None -> t
            | Some (_, us) -> mk (Tm_uinst(t, us))
        end

      | Tm_abs(bs, body, lopt) -> 
        let bs = bs |> List.map (fun (x, imp) -> {x with sort=inst s x.sort}, imp) in
        let body = inst s body in
        mk (Tm_abs(bs, body, inst_lcomp_opt s lopt))

      | Tm_arrow (bs, c) -> 
        let bs = bs |> List.map (fun (x, imp) -> {x with sort=inst s x.sort}, imp) in
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

      | Tm_ascribed(t1, t2, f) -> 
        mk (Tm_ascribed(inst s t1, inst s t2, f))

      | Tm_let(lbs, t) -> 
        let lbs = fst lbs, snd lbs |> List.map (fun lb -> {lb with lbtyp=inst s lb.lbtyp; lbdef=inst s lb.lbdef}) in
        mk (Tm_let(lbs, inst s t))
          
      | Tm_meta(t, Meta_pattern args) -> 
        mk (Tm_meta(inst s t, Meta_pattern (args |> List.map (inst_args s))))

      | Tm_meta(t, tag) -> 
        mk (Tm_meta(inst s t, tag))

and inst_args s args = args |> List.map (fun (a, imp) -> inst s a, imp)

and inst_comp s c = match c.n with 
    | Total t -> S.mk_Total (inst s t)
    | GTotal t -> S.mk_GTotal (inst s t)
    | Comp ct -> let ct = {ct with result_typ=inst s ct.result_typ;
                                   effect_args=inst_args s ct.effect_args;
                                   flags=ct.flags |> List.map (function 
                                        | DECREASES t -> DECREASES (inst s t)
                                        | f -> f)} in
                 S.mk_Comp ct


and inst_lcomp_opt s l = match l with 
    | None -> None
    | Some lc -> 
       Some ({lc with res_typ=inst s lc.res_typ;
                      comp=(fun () -> inst_comp s (lc.comp()))})