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
module FStar.TypeChecker.Generalize

open FStar
open FStar.All
open FStar.Util
open FStar.Errors
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env

module BU    = FStar.Util
module S     = FStar.Syntax.Syntax
module SS    = FStar.Syntax.Subst
module Free  = FStar.Syntax.Free
module U     = FStar.Syntax.Util
module Print = FStar.Syntax.Print
module UF    = FStar.Syntax.Unionfind
module Env   = FStar.TypeChecker.Env
module N     = FStar.TypeChecker.Normalize

(**************************************************************************************)
(* Generalizing types *)
(**************************************************************************************)
let string_of_univs univs =
  BU.set_elements univs
  |> List.map (fun u -> UF.univ_uvar_id u |> string_of_int) |> String.concat ", "

let gen_univs env (x:BU.set<universe_uvar>) : list<univ_name> =
    if BU.set_is_empty x then []
    else let s = BU.set_difference x (Env.univ_vars env) |> BU.set_elements in
         if Env.debug env <| Options.Other "Gen" then
         BU.print1 "univ_vars in env: %s\n" (string_of_univs (Env.univ_vars env));
         let r = Some (Env.get_range env) in
         let u_names = s |> List.map (fun u ->
            let u_name = Syntax.new_univ_name r in
            if Env.debug env <| Options.Other "Gen"
            then BU.print3 "Setting ?%s (%s) to %s\n"
                            (string_of_int <| UF.univ_uvar_id u)
                            (Print.univ_to_string (U_unif u))
                            (Print.univ_to_string (U_name u_name));
            UF.univ_change u (U_name u_name);
            u_name) in
         u_names

let gather_free_univnames env t : list<univ_name> =
    let ctx_univnames = Env.univnames env in
    let tm_univnames = Free.univnames t in
    let univnames = BU.set_difference tm_univnames ctx_univnames |> BU.set_elements in
    // BU.print4 "Closing universe variables in term %s : %s in ctx, %s in tm, %s globally\n"
    //     (Print.term_to_string t)
    //     (Print.set_to_string Ident.string_of_id ctx_univnames)
    //     (Print.set_to_string Ident.string_of_id tm_univnames)
    //     (Print.list_to_string Ident.string_of_id univnames);
    univnames

let check_universe_generalization
  (explicit_univ_names : list<univ_name>)
  (generalized_univ_names : list<univ_name>)
  (t : term)
  : list<univ_name>
=
  match explicit_univ_names, generalized_univ_names with
  | [], _ -> generalized_univ_names
  | _, [] -> explicit_univ_names
  | _ -> raise_error (Errors.Fatal_UnexpectedGeneralizedUniverse, ("Generalized universe in a term containing explicit universe annotation : "
                      ^ Print.term_to_string t)) t.pos

let generalize_universes (env:env) (t0:term) : tscheme =
  Errors.with_ctx "While generalizing universes" (fun () ->
    let t = N.normalize [Env.NoFullNorm; Env.Beta; Env.DoNotUnfoldPureLets] env t0 in
    let univnames = gather_free_univnames env t in
    if Env.debug env <| Options.Other "Gen"
    then BU.print2 "generalizing universes in the term (post norm): %s with univnames: %s\n" (Print.term_to_string t) (Print.univ_names_to_string univnames);
    let univs = Free.univs t in
    if Env.debug env <| Options.Other "Gen"
    then BU.print1 "univs to gen : %s\n" (string_of_univs univs);
    let gen = gen_univs env univs in
    if Env.debug env <| Options.Other "Gen"
    then BU.print2 "After generalization, t: %s and univs: %s\n"  (Print.term_to_string t) (Print.univ_names_to_string gen);
    let univs = check_universe_generalization univnames gen t0 in
    let t = N.reduce_uvar_solutions env t in
    let ts = SS.close_univ_vars univs t in
    univs, ts
  )

let gen env (is_rec:bool) (lecs:list<(lbname * term * comp)>) : option<list<(lbname * list<univ_name> * term * comp * list<binder>)>> =
  if not <| (BU.for_all (fun (_, _, c) -> U.is_pure_or_ghost_comp c) lecs) //No value restriction in F*---generalize the types of pure computations
  then None
  else
     let norm c =
        if debug env Options.Medium
        then BU.print1 "Normalizing before generalizing:\n\t %s\n" (Print.comp_to_string c);
         let c = Normalize.normalize_comp [Env.Beta; Env.Exclude Env.Zeta; Env.NoFullNorm; Env.DoNotUnfoldPureLets] env c in
         if debug env Options.Medium then
            BU.print1 "Normalized to:\n\t %s\n" (Print.comp_to_string c);
         c in
     let env_uvars = Env.uvars_in_env env in
     let gen_uvars uvs = BU.set_difference uvs env_uvars |> BU.set_elements in
     let univs_and_uvars_of_lec (lbname, e, c) =
          let c = norm c in
          let t = U.comp_result c in
          let univs = Free.univs t in
          let uvt = Free.uvars t in
          if Env.debug env <| Options.Other "Gen"
          then BU.print2 "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n"
                (BU.set_elements univs |> List.map (fun u -> Print.univ_to_string (U_unif u)) |> String.concat ", ")
                (BU.set_elements uvt |> List.map (fun u -> BU.format2 "(%s : %s)"
                                                                    (Print.uvar_to_string u.ctx_uvar_head)
                                                                    (Print.term_to_string u.ctx_uvar_typ)) |> String.concat ", ");
          let univs =
            List.fold_left
              (fun univs uv -> BU.set_union univs (Free.univs uv.ctx_uvar_typ))
              univs
             (BU.set_elements uvt) in
          let uvs = gen_uvars uvt in
          if Env.debug env <| Options.Other "Gen"
          then BU.print2 "^^^^\n\tFree univs = %s\n\tgen_uvars =%s"
                (BU.set_elements univs |> List.map (fun u -> Print.univ_to_string (U_unif u)) |> String.concat ", ")
                (uvs |> List.map (fun u -> BU.format2 "(%s : %s)"
                                                        (Print.uvar_to_string u.ctx_uvar_head)
                                                        (N.term_to_string env u.ctx_uvar_typ)) |> String.concat ", ");

         univs, uvs, (lbname, e, c)
     in
     let univs, uvs, lec_hd = univs_and_uvars_of_lec (List.hd lecs) in
     let force_univs_eq lec2 u1 u2 =
        if BU.set_is_subset_of u1 u2
        && BU.set_is_subset_of u2 u1
        then ()
        else let lb1, _, _ = lec_hd in
             let lb2, _, _ = lec2 in
             let msg = BU.format2 "Generalizing the types of these mutually recursive definitions \
                                   requires an incompatible set of universes for %s and %s"
                            (Print.lbname_to_string lb1)
                            (Print.lbname_to_string lb2) in
             raise_error (Errors.Fatal_IncompatibleSetOfUniverse, msg) (Env.get_range env)
     in
     let force_uvars_eq lec2 (u1:list<ctx_uvar>) (u2:list<ctx_uvar>) =
        let uvars_subseteq u1 u2 =
            u1 |> BU.for_all (fun u ->
            u2 |> BU.for_some (fun u' -> UF.equiv u.ctx_uvar_head u'.ctx_uvar_head))
        in
        if uvars_subseteq u1 u2
        && uvars_subseteq u2 u1
        then ()
        else let lb1, _, _ = lec_hd in
             let lb2, _, _ = lec2 in
             let msg = BU.format2 "Generalizing the types of these mutually recursive definitions \
                                   requires an incompatible number of types for %s and %s"
                            (Print.lbname_to_string lb1)
                            (Print.lbname_to_string lb2) in
             raise_error (Errors.Fatal_IncompatibleNumberOfTypes, msg) (Env.get_range env)
     in

     let lecs =
        List.fold_right (fun this_lec lecs ->
           let this_univs, this_uvs, this_lec = univs_and_uvars_of_lec this_lec in
           force_univs_eq this_lec univs this_univs;
           force_uvars_eq this_lec uvs this_uvs;
           this_lec::lecs)
        (List.tl lecs)
        []
     in

     let lecs = lec_hd :: lecs in

     let gen_types (uvs:list<ctx_uvar>) : list<(bv * aqual)> =
         let fail rng k : unit =
             let lbname, e, c = lec_hd in
               raise_error (Errors.Fatal_FailToResolveImplicitArgument,
                            BU.format3 "Failed to resolve implicit argument of type '%s' in the type of %s (%s)"
                                       (Print.term_to_string k)
                                       (Print.lbname_to_string lbname)
                                       (Print.term_to_string (U.comp_result c)))
                            rng
         in
         uvs |> List.map (fun u ->
         match UF.find u.ctx_uvar_head with
         | Some _ -> failwith "Unexpected instantiation of mutually recursive uvar"
         | _ ->
           let k = N.normalize [Env.Beta; Env.Exclude Env.Zeta] env u.ctx_uvar_typ in
           let bs, kres = U.arrow_formals k in
           let _ =
             //we only generalize variables at type k = a:Type{phi}
             //where k is closed
             //this is in support of ML-style polymorphism, while also allowing generalizing
             //over things like eqtype, which is a common case
             //Otherwise, things go badly wrong: see #1091
             match (U.unrefine (N.unfold_whnf env kres)).n with
             | Tm_type _ ->
                let free = FStar.Syntax.Free.names kres in
                if not (BU.set_is_empty free) then fail u.ctx_uvar_range kres

             | _ ->
               fail u.ctx_uvar_range kres
           in
           let a = S.new_bv (Some <| Env.get_range env) kres in
           let t =
               match bs with
               | [] -> S.bv_to_name a
               | _ -> U.abs bs (S.bv_to_name a) (Some (U.residual_tot kres))
           in
           U.set_uvar u.ctx_uvar_head t;
            //t clearly has a free variable; this is the one place we break the
            //invariant of a uvar always being resolved to a term well-typed in its given context
           a, Some S.imp_tag)
     in

     let gen_univs = gen_univs env univs in
     let gen_tvars = gen_types uvs in

     let ecs = lecs |> List.map (fun (lbname, e, c) ->
         let e, c, gvs =
            match gen_tvars, gen_univs with
            | [], [] ->
              //nothing generalized
              e, c, []

            | _ ->
              //before we manipulate the term further, we must normalize it to get rid of the invariant-broken uvars
              let e0, c0 = e, c in
              let c = N.normalize_comp [Env.Beta; Env.DoNotUnfoldPureLets; Env.CompressUvars; Env.NoFullNorm; Env.Exclude Env.Zeta] env c in
              let e = N.reduce_uvar_solutions env e in
              let e =
                if is_rec
                then let tvar_args = List.map (fun (x, _) -> S.iarg (S.bv_to_name x)) gen_tvars in
                     let instantiate_lbname_with_app tm fv =
                        if S.fv_eq fv (right lbname)
                        then S.mk_Tm_app tm tvar_args tm.pos
                        else tm
                    in FStar.Syntax.InstFV.inst instantiate_lbname_with_app e
                else e
              in
              //now, with the uvars gone, we can close over the newly introduced type names
              let tvars_bs = gen_tvars |> List.map (fun (x, q) -> {binder_bv=x; binder_qual=q; binder_attrs=[]}) in
              let t = match (SS.compress (U.comp_result c)).n with
                    | Tm_arrow(bs, cod) ->
                      let bs, cod = SS.open_comp bs cod in
                      U.arrow (tvars_bs@bs) cod

                    | _ ->
                      U.arrow tvars_bs c in
              let e' = U.abs tvars_bs e (Some (U.residual_comp_of_comp c)) in
              e', S.mk_Total t, tvars_bs in
          (lbname, gen_univs, e, c, gvs)) in
     Some ecs

let generalize' env (is_rec:bool) (lecs:list<(lbname*term*comp)>) : (list<(lbname*univ_names*term*comp*list<binder>)>) =
  assert (List.for_all (fun (l, _, _) -> is_right l) lecs); //only generalize top-level lets
  if debug env Options.Low
  then BU.print1 "Generalizing: %s\n"
       (List.map (fun (lb, _, _) -> Print.lbname_to_string lb) lecs |> String.concat ", ");
  let univnames_lecs = List.map (fun (l, t, c) -> gather_free_univnames env t) lecs in
  let generalized_lecs =
      match gen env is_rec lecs with
          | None -> lecs |> List.map (fun (l,t,c) -> l,[],t,c,[])
          | Some luecs ->
            if debug env Options.Medium
            then luecs |> List.iter
                    (fun (l, us, e, c, gvs) ->
                         BU.print5 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                          (Range.string_of_range e.pos)
                                          (Print.lbname_to_string l)
                                          (Print.term_to_string (U.comp_result c))
                                          (Print.term_to_string e)
                                          (Print.binders_to_string ", " gvs));
            luecs
   in
   List.map2 (fun univnames (l,generalized_univs, t, c, gvs) ->
              (l, check_universe_generalization univnames generalized_univs t, t, c, gvs))
             univnames_lecs
             generalized_lecs

let generalize env is_rec lecs = 
  Errors.with_ctx "While generalizing" (fun () ->
    Profiling.profile (fun () -> generalize' env is_rec lecs)
                      (Some (Ident.string_of_lid (Env.current_module env)))
                      "FStar.TypeChecker.Util.generalize"
  )
