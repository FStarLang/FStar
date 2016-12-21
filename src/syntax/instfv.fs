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
open FStar.Util
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U = FStar.Util
type inst_t = list<(lident * universes)>

// VALS_HACK_HERE

let mk t s = S.mk s !t.tk t.pos

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
      | Tm_unknown
      | Tm_uinst _ -> t

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

      | Tm_ascribed(t1, Inl t2, f) ->
        mk (Tm_ascribed(inst s t1, Inl (inst s t2), f))

      | Tm_ascribed(t1, Inr c, f) ->
        mk (Tm_ascribed(inst s t1, Inr (inst_comp s c), f))

      | Tm_let(lbs, t) ->
        let lbs = fst lbs, snd lbs |> List.map (fun lb -> {lb with lbtyp=inst s lb.lbtyp; lbdef=inst s lb.lbdef}) in
        mk (Tm_let(lbs, inst s t))

      | Tm_meta(t, Meta_pattern args) ->
        mk (Tm_meta(inst s t, Meta_pattern (args |> List.map (inst_args s))))

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
    | None
    | Some (Inr _) -> l
    | Some (Inl lc) ->
       Some (Inl ({lc with res_typ=inst s lc.res_typ;
                           comp=(fun () -> inst_comp s (lc.comp()))}))

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


(* Given a list of bundled type declarations potentially with type
   abbreviations, construct the new bundle without type abbreviations
   or lets (where they have been all unfolded) and the list of type
   abbreviations or lets separated away from the bundle (and sorted in
   dependency order, in such a way that they are no longer mutually
   recursive.)  *)

let disentangle_abbrevs_from_bundle
    (sigelts: list<sigelt>)
    (quals:   list<qualifier>)
    (members: list<lident>)
    (rng:   FStar.Range.range)
    : sigelt * list<sigelt> =

    (* Gather the list of type abbrevs *)
   let type_abbrev_sigelts = sigelts |> List.collect begin fun x -> match x with
       | Sig_let ((false, [ { lbname= Inr _ } ]), _, _, _) -> [x]
       | Sig_let (_, _, _, _) ->
         failwith "instfv: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
       | _ -> []
   end
   in

   match type_abbrev_sigelts with
   | [] ->
     (* if there are no type abbreviations, then do not change anything. *)
     (Sig_bundle (sigelts, quals, members, rng), [])
   | _ ->

    let type_abbrevs = type_abbrev_sigelts |> List.map begin function
        | Sig_let ((_, [ { lbname = Inr fv } ] ) , _, _, _) -> fv.fv_name.v
        | _ -> failwith "instfv: disentangle_abbrevs_from_bundle: type_abbrevs: impossible"
    end
    in

    (* First, unfold type abbrevs among themselves *)
    let unfolded_type_abbrevs =

        (* List of type abbreviations that have been unfolded, in
        reverse order (from most recent to most ancient: the head
        depends on the tail.) *)
        let rev_unfolded_type_abbrevs : ref<(list<sigelt>)> = U.mk_ref [] in

        (* List of names of type abbreviations whose unfolding has
        started. If they occur during renaming of the current type
        abbreviation, then there is a cycle. Follows a stack
        discipline. *)
        let in_progress : ref<(list<lident>)> = U.mk_ref [] in

        (* List of type abbreviations that have not been unfolded
        yet. Their order can change, since anyway they will be
        reordered after being unfolded. *)
        let not_unfolded_yet = U.mk_ref type_abbrev_sigelts in

        let remove_not_unfolded lid =
            not_unfolded_yet := !not_unfolded_yet |> List.filter begin function
                | Sig_let ((_, [ { lbname = Inr fv } ] ) , _, _, _) ->
                  not (lid_equals lid fv.fv_name.v)
                | _ -> true
            end
        in
    
        (* Replace a free variable corresponding to a type
        abbreviation, with memoization. *)
        let rec unfold_abbrev_fv (t: term) (fv : S.fv) : term =
            let replacee x = match x with
                | Sig_let ((_, [ { lbname = Inr fv' } ] ) , _, _, _)
                  when lid_equals fv'.fv_name.v fv.fv_name.v ->
                  Some x
                | _ -> None
            in
            let replacee_term x = match replacee x with
                | Some (Sig_let ((_, [ { lbdef = tm } ] ) , _, _, _)) -> Some tm
                | _ -> None
            in
            match U.find_map !rev_unfolded_type_abbrevs replacee_term with
                | Some x -> x
                | None ->
                  begin match U.find_map type_abbrev_sigelts replacee with
                      | Some se ->
                          if FStar.List.existsb (fun x -> lid_equals x fv.fv_name.v) !in_progress
                          then let msg = U.format1 "Cycle on %s in mutually recursive type abbreviations" fv.fv_name.v.str in
                               raise (Error (msg, range_of_lid fv.fv_name.v))
                          else unfold_abbrev se
                      | _ -> t
                  end

        (* Start unfolding in a type abbreviation that has not occurred before. *)
        and unfold_abbrev = function
            | Sig_let ((false, [lb]) , rng, _, quals) ->
                let lid = match lb.lbname with
                    | Inr fv -> fv.fv_name.v
                    | _ -> failwith "instfv: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible"
                in
                let () = in_progress := lid :: !in_progress in  (* push *)
                let () = remove_not_unfolded lid in
                let ty' = inst unfold_abbrev_fv lb.lbtyp in
                let tm' = inst unfold_abbrev_fv lb.lbdef in
                let lb' = { lb with lbtyp = ty' ; lbdef = tm' } in
                let sigelt' = Sig_let ((false, [lb']), rng, [lid], quals) in
                let () = rev_unfolded_type_abbrevs := sigelt' :: !rev_unfolded_type_abbrevs in
                let () = in_progress := List.tl !in_progress in (* pop *)
                ty'
            | _ -> failwith "instfv: disentangle_abbrevs_from_bundle: rename_abbrev: impossible"
        in
            
        let rec aux () = match !not_unfolded_yet with
            | x :: _ -> let _unused = unfold_abbrev x in aux ()
            | _ -> List.rev !rev_unfolded_type_abbrevs

        in

        aux ()
      in

      (* Now, unfold in inductive types and data constructors *)

      let filter_out_type_abbrevs l =
          List.filter (fun lid -> FStar.List.for_all (fun lid' -> not (lid_equals lid lid')) type_abbrevs) l
      in
      
      let inductives_with_abbrevs_unfolded =

          let find_in_unfolded fv = U.find_map unfolded_type_abbrevs begin fun x -> match x with
              | Sig_let ((_, [ { lbname = Inr fv' ; lbdef = tm } ] ), _, _, _) when (lid_equals fv'.fv_name.v fv.fv_name.v) ->
                Some tm
              | _ -> None
          end
          in

          let unfold_fv (t: term) (fv: S.fv) : term = match find_in_unfolded fv with
              | Some t' -> t'
              | _ -> t
          in

          let unfold_in_sig = function
              | Sig_inductive_typ (lid, univs, bnd, ty, mut, dc, quals, rng) ->
                let bnd' = inst_binders unfold_fv bnd in
                let ty'  = inst unfold_fv ty in
                let mut' = filter_out_type_abbrevs mut in
                [Sig_inductive_typ (lid, univs, bnd', ty', mut', dc, quals, rng)]

              | Sig_datacon (lid, univs, ty, res, npars, quals, mut, rng) ->
                let ty' = inst unfold_fv ty in
                let mut' = filter_out_type_abbrevs mut in
                [Sig_datacon (lid, univs, ty', res, npars, quals, mut', rng)]

              | Sig_let (_, _, _, _) ->
                []

              | _ -> failwith "instfv: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible"
           in

           List.collect unfold_in_sig sigelts
      in

      (* Finally, construct a new bundle separate from type abbrevs *)

      let new_members = filter_out_type_abbrevs members
      in

      let new_bundle = Sig_bundle (inductives_with_abbrevs_unfolded, quals, new_members, rng)
      in

      (new_bundle, unfolded_type_abbrevs)
