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
module FStarC.TypeChecker.Generalize

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Util
open FStarC.Errors
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.TypeChecker.Env

open FStarC.Class.Show
open FStarC.Syntax.Print {}
open FStarC.Class.Setlike

module BU    = FStarC.Util
module S     = FStarC.Syntax.Syntax
module SS    = FStarC.Syntax.Subst
module Free  = FStarC.Syntax.Free
module U     = FStarC.Syntax.Util
module UF    = FStarC.Syntax.Unionfind
module Env   = FStarC.TypeChecker.Env
module N     = FStarC.TypeChecker.Normalize

let dbg_Gen = Debug.get_toggle "Gen"

instance showable_univ_var : showable universe_uvar = {
  show = (fun u -> show (U_unif u));
}

(**************************************************************************************)
(* Generalizing types *)
(**************************************************************************************)

let gen_univs env (x:FlatSet.t universe_uvar) : list univ_name =
    if is_empty x then []
    else let s = diff x (Env.univ_vars env) |> elems in // GGG: bad, order dependent
         if !dbg_Gen then
           BU.print1 "univ_vars in env: %s\n" (show (Env.univ_vars env));
         let r = Some (Env.get_range env) in
         let u_names = s |> List.map (fun u ->
           let u_name = Syntax.new_univ_name r in
           if !dbg_Gen then
            BU.print3 "Setting ?%s (%s) to %s\n"
                            (string_of_int <| UF.univ_uvar_id u)
                            (show (U_unif u))
                            (show (U_name u_name));
           UF.univ_change u (U_name u_name);
           u_name)
         in
         u_names

let gather_free_univnames env t : FlatSet.t univ_name =
    let ctx_univnames = Env.univnames env in
    let tm_univnames = Free.univnames t in
    let univnames = diff tm_univnames ctx_univnames in
    // BU.print4 "Closing universe variables in term %s : %s in ctx, %s in tm, %s globally\n"
    //     (show t)
    //     (Common.string_of_set Ident.string_of_id ctx_univnames)
    //     (Common.string_of_set Ident.string_of_id tm_univnames)
    //     (Common.string_of_list Ident.string_of_id univnames);
    univnames

let check_universe_generalization
  (explicit_univ_names : list univ_name)
  (generalized_univ_names : list univ_name)
  (t : term)
  : list univ_name
=
  match explicit_univ_names, generalized_univ_names with
  | [], _ -> generalized_univ_names
  | _, [] -> explicit_univ_names
  | _ -> raise_error t Errors.Fatal_UnexpectedGeneralizedUniverse
           ("Generalized universe in a term containing explicit universe annotation : " ^ show t)

let generalize_universes (env:env) (t0:term) : tscheme =
  Errors.with_ctx "While generalizing universes" (fun () ->
    let t = N.normalize [Env.NoFullNorm; Env.Beta; Env.DoNotUnfoldPureLets] env t0 in
    let univnames = elems (gather_free_univnames env t) in /// GGG: bad, order dependent
    if !dbg_Gen
    then BU.print2 "generalizing universes in the term (post norm): %s with univnames: %s\n" (show t) (show univnames);
    let univs = Free.univs t in
    if !dbg_Gen
    then BU.print1 "univs to gen : %s\n" (show univs);
    let gen = gen_univs env univs in
    if !dbg_Gen
    then BU.print2 "After generalization, t: %s and univs: %s\n"  (show t) (show gen);
    let univs = check_universe_generalization univnames gen t0 in
    let t = N.reduce_uvar_solutions env t in
    let ts = SS.close_univ_vars univs t in
    univs, ts
  )

let gen env (is_rec:bool) (lecs:list (lbname & term & comp)) : option (list (lbname & list univ_name & term & comp & list binder)) =
  if not <| (BU.for_all (fun (_, _, c) -> U.is_pure_or_ghost_comp c) lecs) //No value restriction in F*---generalize the types of pure computations
  then None
  else
     let norm c =
        if Debug.medium ()
        then BU.print1 "Normalizing before generalizing:\n\t %s\n" (show c);
         let c = Normalize.normalize_comp [Env.Beta; Env.Exclude Env.Zeta; Env.NoFullNorm; Env.DoNotUnfoldPureLets] env c in
         if Debug.medium () then
            BU.print1 "Normalized to:\n\t %s\n" (show c);
         c in
     let env_uvars = Env.uvars_in_env env in
     let gen_uvars uvs = diff uvs env_uvars |> elems in /// GGG: bad, order depenedent
     let univs_and_uvars_of_lec (lbname, e, c) =
          let c = norm c in
          let t = U.comp_result c in
          let univs = Free.univs t in
          let uvt = Free.uvars t in
          if !dbg_Gen
          then BU.print2 "^^^^\n\tFree univs = %s\n\tFree uvt=%s\n"
                (show univs) (show uvt);
          let univs =
            List.fold_left
              (fun univs uv -> union univs (Free.univs (U.ctx_uvar_typ uv)))
              univs
             (elems uvt) // Bad; order dependent
          in
          let uvs = gen_uvars uvt in
          if !dbg_Gen
          then BU.print2 "^^^^\n\tFree univs = %s\n\tgen_uvars = %s\n"
                (show univs) (show uvs);

         univs, uvs, (lbname, e, c)
     in
     let univs, uvs, lec_hd = univs_and_uvars_of_lec (List.hd lecs) in
     let force_univs_eq lec2 u1 u2 =
        if equal u1 u2
        then ()
        else let lb1, _, _ = lec_hd in
             let lb2, _, _ = lec2 in
             let msg = BU.format2 "Generalizing the types of these mutually recursive definitions \
                                   requires an incompatible set of universes for %s and %s"
                            (show lb1)
                            (show lb2) in
             raise_error env Errors.Fatal_IncompatibleSetOfUniverse msg
     in
     let force_uvars_eq lec2 (u1:list ctx_uvar) (u2:list ctx_uvar) =
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
                            (show lb1)
                            (show lb2) in
             raise_error env Errors.Fatal_IncompatibleNumberOfTypes msg
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

     let gen_types (uvs:list ctx_uvar) : list (bv & bqual) =
         uvs |> List.concatMap (fun u ->
         (* If this implicit has a meta, don't generalize it. Just leave it
         unresolved for the resolve_implicits phase to fill it in. *)
         if Some? u.ctx_uvar_meta then [] else

         match UF.find u.ctx_uvar_head with
         | Some _ -> failwith "Unexpected instantiation of mutually recursive uvar"
         | _ ->
           let k = N.normalize [Env.Beta; Env.Exclude Env.Zeta] env (U.ctx_uvar_typ u) in
           let bs, kres = U.arrow_formals k in
           //we only generalize variables at type k = a:Type{phi}
           //where k is closed
           //this is in support of ML-style polymorphism, while also allowing generalizing
           //over things like eqtype, which is a common case
           //Otherwise, things go badly wrong: see #1091
           match (U.unrefine (N.unfold_whnf env kres)).n with
           | Tm_type _ ->
              let free = FStarC.Syntax.Free.names kres in
              if not (is_empty free) then
                []
              else
              let a = S.new_bv (Some <| Env.get_range env) kres in
              let t =
                  match bs with
                  | [] -> S.bv_to_name a
                  | _ -> U.abs bs (S.bv_to_name a) (Some (U.residual_tot kres))
              in
              U.set_uvar u.ctx_uvar_head t;
               //t clearly has a free variable; this is the one place we break the
               //invariant of a uvar always being resolved to a term well-typed in its given context
              [a, S.as_bqual_implicit true]

           | _ ->
             (* This uvar was not a type. Do not generalize it and
             leave the rest of typechecker attempt solving it, or fail *)
             []
         )
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
                    in FStarC.Syntax.InstFV.inst instantiate_lbname_with_app e
                else e
              in
              //now, with the uvars gone, we can close over the newly introduced type names
              let tvars_bs = gen_tvars |> List.map (fun (x, q) -> S.mk_binder_with_attrs x q None []) in
              let t = match (SS.compress (U.comp_result c)).n with
                    | Tm_arrow {bs; comp=cod} ->
                      let bs, cod = SS.open_comp bs cod in
                      U.arrow (tvars_bs@bs) cod

                    | _ ->
                      U.arrow tvars_bs c in
              let e' = U.abs tvars_bs e (Some (U.residual_comp_of_comp c)) in
              e', S.mk_Total t, tvars_bs in
          (lbname, gen_univs, e, c, gvs))
     in
     Some ecs

let generalize' env (is_rec:bool) (lecs:list (lbname&term&comp)) : (list (lbname&univ_names&term&comp&list binder)) =
  assert (List.for_all (fun (l, _, _) -> is_right l) lecs); //only generalize top-level lets
  if Debug.low () then
     BU.print1 "Generalizing: %s\n"
       (show <| List.map (fun (lb, _, _) -> show lb) lecs);
  let univnames_lecs = 
    let empty = from_list [] in
    List.fold_left
      (fun out (l, t, c) -> 
          union out (gather_free_univnames env t))
      empty
      lecs
  in
  let univnames_lecs = elems univnames_lecs in /// GGG: bad, order dependent
  let generalized_lecs =
      match gen env is_rec lecs with
          | None -> lecs |> List.map (fun (l,t,c) -> l,[],t,c,[])
          | Some luecs ->
            if Debug.medium ()
            then luecs |> List.iter
                    (fun (l, us, e, c, gvs) ->
                         BU.print5 "(%s) Generalized %s at type %s\n%s\nVars = (%s)\n"
                                          (show e.pos)
                                          (show l)
                                          (show (U.comp_result c))
                                          (show e)
                                          (show gvs));
            luecs
   in
   List.map (fun (l, generalized_univs, t, c, gvs) ->
              (l, check_universe_generalization univnames_lecs generalized_univs t, t, c, gvs))
             generalized_lecs

let generalize env is_rec lecs = 
  Errors.with_ctx "While generalizing" (fun () ->
    Profiling.profile (fun () -> generalize' env is_rec lecs)
                      (Some (Ident.string_of_lid (Env.current_module env)))
                      "FStarC.TypeChecker.Util.generalize"
  )
