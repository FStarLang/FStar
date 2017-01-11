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
module FStar.Syntax.MutRecTy
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Util
open FStar.Errors
open FStar.Syntax.InstFV
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module U = FStar.Util


// VALS_HACK_HERE

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
       | Sig_let ((false, [ { lbname= Inr _ } ]), _, _, _, _) -> [x]
       | Sig_let (_, _, _, _, _) ->
         failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrev_sigelts: impossible"
       | _ -> []
   end
   in

   match type_abbrev_sigelts with
   | [] ->
     (* if there are no type abbreviations, then do not change anything. *)
     (Sig_bundle (sigelts, quals, members, rng), [])
   | _ ->

    let type_abbrevs = type_abbrev_sigelts |> List.map begin function
        | Sig_let ((_, [ { lbname = Inr fv } ] ) , _, _, _, _) -> fv.fv_name.v
        | _ -> failwith "mutrecty: disentangle_abbrevs_from_bundle: type_abbrevs: impossible"
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
                | Sig_let ((_, [ { lbname = Inr fv } ] ) , _, _, _, _) ->
                  not (lid_equals lid fv.fv_name.v)
                | _ -> true
            end
        in
    
        (* Replace a free variable corresponding to a type
        abbreviation, with memoization. *)
        let rec unfold_abbrev_fv (t: term) (fv : S.fv) : term =
            let replacee x = match x with
                | Sig_let ((_, [ { lbname = Inr fv' } ] ) , _, _, _, _)
                  when lid_equals fv'.fv_name.v fv.fv_name.v ->
                  Some x
                | _ -> None
            in
            let replacee_term x = match replacee x with
                | Some (Sig_let ((_, [ { lbdef = tm } ] ) , _, _, _, _)) -> Some tm
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
            | Sig_let ((false, [lb]) , rng, _, quals, attr) ->
	        (* eliminate some qualifiers for definitions *)
	        let quals = quals |> List.filter begin function
	        | Noeq -> false
	        | _ -> true
	        end in
                let lid = match lb.lbname with
                    | Inr fv -> fv.fv_name.v
                    | _ -> failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: lid: impossible"
                in
                let () = in_progress := lid :: !in_progress in  (* push *)
                let () = remove_not_unfolded lid in
                let ty' = inst unfold_abbrev_fv lb.lbtyp in
                let tm' = inst unfold_abbrev_fv lb.lbdef in
                let lb' = { lb with lbtyp = ty' ; lbdef = tm' } in
                let sigelt' = Sig_let ((false, [lb']), rng, [lid], quals, attr) in
                let () = rev_unfolded_type_abbrevs := sigelt' :: !rev_unfolded_type_abbrevs in
                let () = in_progress := List.tl !in_progress in (* pop *)
                tm'
            | _ -> failwith "mutrecty: disentangle_abbrevs_from_bundle: rename_abbrev: impossible"
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
              | Sig_let ((_, [ { lbname = Inr fv' ; lbdef = tm } ] ), _, _, _, _) when (lid_equals fv'.fv_name.v fv.fv_name.v) ->
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

              | Sig_let (_, _, _, _, _) ->
                []

              | _ -> failwith "mutrecty: inductives_with_abbrevs_unfolded: unfold_in_sig: impossible"
           in

           List.collect unfold_in_sig sigelts
      in

      (* Finally, construct a new bundle separate from type abbrevs *)

      let new_members = filter_out_type_abbrevs members
      in

      let new_bundle = Sig_bundle (inductives_with_abbrevs_unfolded, quals, new_members, rng)
      in

      (new_bundle, unfolded_type_abbrevs)
