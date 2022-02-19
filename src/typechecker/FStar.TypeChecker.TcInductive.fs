(*
   Copyright 2008-2014 Microsoft Research

   Authors: Nikhil Swamy, Aseem Rastogi

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
module FStar.TypeChecker.TcInductive
open FStar.Pervasives
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar
open FStar.Compiler
open FStar.Errors
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Compiler.Util
open FStar.Ident
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Syntax.Subst
open FStar.Syntax.Util
open FStar.Const
open FStar.TypeChecker.Rel
open FStar.TypeChecker.Common
open FStar.TypeChecker.TcTerm
module S  = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module N  = FStar.TypeChecker.Normalize
module TcUtil = FStar.TypeChecker.Util
module Gen = FStar.TypeChecker.Generalize
module BU = FStar.Compiler.Util //basic util
module U  = FStar.Syntax.Util
module PP = FStar.Syntax.Print
module C  = FStar.Parser.Const

let unfold_whnf = N.unfold_whnf' [Env.AllowUnboundUniverses]

let tc_tycon (env:env_t)     (* environment that contains all mutually defined type constructors *)
             (s:sigelt)      (* a Sig_inductive_type (aka tc) that needs to be type-checked *)
       : env_t          (* environment extended with a refined type for the type-constructor *)
       * sigelt         (* the typed version of s, with universe variables still TBD *)
       * universe       (* universe of the constructed type *)
       * guard_t        (* constraints on implicit variables *)
 = match s.sigel with
   | Sig_inductive_typ (tc, uvs, tps, k, mutuals, data) -> //the only valid qual is Private
         //assert (uvs = []); AR: not necessarily true in two phase
         let env0 = env in
 (*open*)let usubst, uvs = SS.univ_var_opening uvs in
         let env, tps, k = Env.push_univ_vars env uvs, SS.subst_binders usubst tps, SS.subst (SS.shift_subst (List.length tps) usubst) k in
         let tps, k = SS.open_term tps k in
         let tps, env_tps, guard_params, us = tc_binders env tps in

         (*
          * AR: typecheck k and get the indices and t out
          *     adding a very restricted normalization to unfold symbols that are marked unfold explicitly
          *     note that t is opened with indices (by U.arrow_formals)
          *)
         let (indices, t), guard =
           let k, _, g = tc_tot_or_gtot_term env_tps k in
           let k = N.normalize [Exclude Iota; Exclude Zeta; Eager_unfolding; NoFullNorm; Exclude Beta] env_tps k in
           U.arrow_formals k, Rel.discharge_guard env_tps (Env.conj_guard guard_params g)
         in

         let k = U.arrow indices (S.mk_Total t) in
         let t_type, u = U.type_u() in
         //AR: allow only Type and eqtype, nothing else
         let valid_type = (U.is_eqtype_no_unrefine t && not (s.sigquals |> List.contains Unopteq)) ||
                          (teq_nosmt_force env t t_type) in
         if not valid_type then
             raise_error (Errors.Error_InductiveAnnotNotAType,
                          (BU.format2 "Type annotation %s for inductive %s is not Type or eqtype, or it is eqtype but contains unopteq qualifier"
                                                (Print.term_to_string t)
                                                (Ident.string_of_lid tc))) s.sigrng;

(*close*)let usubst = SS.univ_var_closing uvs in
         let guard = TcUtil.close_guard_implicits env false tps guard in
         let t_tc = U.arrow ((tps |> SS.subst_binders usubst) @
                             (indices |> SS.subst_binders (SS.shift_subst (List.length tps) usubst)))
                            (S.mk_Total (t |> SS.subst (SS.shift_subst (List.length tps + List.length indices) usubst))) in
         let tps = SS.close_binders tps in
         let k = SS.close tps k in
         let tps, k = SS.subst_binders usubst tps, SS.subst (SS.shift_subst (List.length tps) usubst) k in
         let fv_tc = S.lid_as_fv tc delta_constant None in
         let (uvs, t_tc) = SS.open_univ_vars uvs t_tc in
         Env.push_let_binding env0 (Inr fv_tc) (uvs, t_tc),
         { s with sigel = Sig_inductive_typ(tc, uvs, tps, k, mutuals, data) },
         u,
         guard

    | _ -> failwith "impossible"


(* 2. Checking each datacon *)
let tc_data (env:env_t) (tcs : list<(sigelt * universe)>)
  : sigelt -> sigelt * guard_t =
    fun se -> match se.sigel with
    | Sig_datacon(c, _uvs, t, tc_lid, ntps, mutual_tcs) ->
         //assert (_uvs = []);
         let usubst, _uvs = SS.univ_var_opening _uvs in
         let env, t = Env.push_univ_vars env _uvs, SS.subst usubst t in
         let (env, tps, u_tc) = //u_tc is the universe of the inductive that c constructs
            let tps_u_opt = BU.find_map tcs (fun (se, u_tc) ->
                if lid_equals tc_lid (must (U.lid_of_sigelt se))
                then match se.sigel with
                     | Sig_inductive_typ(_, _, tps, _, _, _) ->
                        let tps = tps |> SS.subst_binders usubst |> List.map (fun x -> {x with binder_qual=Some S.imp_tag}) in
                        let tps = Subst.open_binders tps in
                        Some (Env.push_binders env tps, tps, u_tc)
                     | _ -> failwith "Impossible"
                else None) in
            match tps_u_opt with
             | Some x -> x
             | None ->
               if lid_equals tc_lid FStar.Parser.Const.exn_lid
               then env, [], U_zero
               else raise_error (Errors.Fatal_UnexpectedDataConstructor, ("Unexpected data constructor")) se.sigrng
         in

         let arguments, result =
            let t = N.normalize (N.whnf_steps @ [Env.AllowUnboundUniverses]) env t in  //AR: allow unbounded universes, since we haven't typechecked t yet
            match (SS.compress t).n with
                | Tm_arrow(bs, res) ->
                  //the type of each datacon is already a function with the type params as arguments
                  //need to map the prefix of bs corresponding to params to the tps of the inductive
                  let _, bs' = BU.first_N ntps bs in
                  let t = mk (Tm_arrow(bs', res)) t.pos in
                  let subst = tps |> List.mapi (fun i ({binder_bv=x}) -> DB(ntps - (1 + i), x)) in
(*open*)          let bs, c = U.arrow_formals_comp (SS.subst subst t) in
                  (* check that c is a Tot computation, reject it otherwise
                   * (unless --MLish, which will mark all of them with ML effect) *)
                  if Options.ml_ish () || is_total_comp c
                  then bs, comp_result c
                  else raise_error (Errors.Fatal_UnexpectedConstructorType,
                                     "Constructors cannot have effects")
                                   (range_of_lid (U.comp_effect_name c))

                | _ -> [], t
         in

         if Env.debug env Options.Low then BU.print3 "Checking datacon  %s : %s -> %s \n"
                (Print.lid_to_string c)
                (Print.binders_to_string "->" arguments)
                (Print.term_to_string result);

         let arguments, env', us = tc_tparams env arguments in
         let type_u_tc = S.mk (Tm_type u_tc) result.pos in
         let env' = Env.set_expected_typ env' type_u_tc in
         let result, res_lcomp = tc_trivial_guard env' result in
         let head, args = U.head_and_args_full result in (* collect nested applications too *)

         (* Make sure the parameters are respected, cf #1534 *)
         (* The first few arguments, as many as List.length tps, must exactly match the
          * bvs in tps, as they have been opened already by the code above. Must be done
          * after typechecking `result`, to make sure implicits are filled in. However,
          * we stop if we logged an error, since it may mean the result type is missing
          * some parameters, and we'd crash when trying to extract them. See issue
          * #2167. *)
         Errors.stop_if_err ();
         let p_args = fst (BU.first_N (List.length tps) args) in
         List.iter2 (fun ({binder_bv=bv}) (t, _) ->
            match (SS.compress t).n with
            | Tm_name bv' when S.bv_eq bv bv' -> ()
            | _ ->
               raise_error (Errors.Error_BadInductiveParam,
                    BU.format2 "This parameter is not constant: expected %s, got %s"
                            (Print.bv_to_string bv) (Print.term_to_string t)) t.pos
         ) tps p_args;

         let ty = unfold_whnf env res_lcomp.res_typ |> U.unrefine in
         begin match (SS.compress ty).n with
               | Tm_type _ -> ()
               | _ -> raise_error (Errors.Fatal_WrongResultTypeAfterConstrutor, (BU.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                (Print.term_to_string result)
                                                (Print.term_to_string ty))) se.sigrng
         end;
         (*
          * AR: if the inductive type is explictly universe annotated,
          *     we need to instantiate universes properly in head (head = tycon<applied to uvars>)
          *     the following code unifies them with the annotated universes
          *)
         let g_uvs = match (SS.compress head).n with
            | Tm_uinst ( { n = Tm_fvar fv }, tuvs)  when S.fv_eq_lid fv tc_lid ->  //AR: in the second phase of 2-phases, this can be a Tm_uninst too
              if List.length _uvs = List.length tuvs then
                List.fold_left2 (fun g u1 u2 ->
                  //unify the two
                  Env.conj_guard g (Rel.teq env' (mk (Tm_type u1) Range.dummyRange) (mk (Tm_type (U_name u2)) Range.dummyRange))
                ) Env.trivial_guard tuvs _uvs
              else Errors.raise_error (Errors.Fatal_UnexpectedConstructorType,
                                       "Length of annotated universes does not match inferred universes")
                                       se.sigrng
            | Tm_fvar fv when S.fv_eq_lid fv tc_lid -> Env.trivial_guard
            | _ -> raise_error (Errors.Fatal_UnexpectedConstructorType, (BU.format2 "Expected a constructor of type %s; got %s"
                                        (Print.lid_to_string tc_lid)
                                        (Print.term_to_string head))) se.sigrng in
         let g =List.fold_left2 (fun g ({binder_bv=x}) u_x ->
                Env.conj_guard g (Rel.universe_inequality u_x u_tc))
            g_uvs
            arguments
            us in

(*close*)let t = U.arrow ((tps |> List.map (fun b -> {b with binder_qual=Some (Implicit true)}))@arguments) (S.mk_Total result) in
                        //NB: the tps are tagged as Implicit inaccessbile arguments of the data constructor
         let t = SS.close_univ_vars _uvs t in
         { se with sigel = Sig_datacon(c, _uvs, t, tc_lid, ntps, mutual_tcs) },
         g

   | _ -> failwith "impossible"


(* 3. Generalizing universes and 4. instantiate inductives within the datacons *)
let generalize_and_inst_within (env:env_t) (tcs:list<(sigelt * universe)>) (datas:list<sigelt>)
    : list<sigelt> * list<sigelt>
    =   //We build a single arrow term of the form
        //   tc_1 -> .. -> tc_n -> dt_1 -> .. dt_n -> Tot unit
        //for each type constructor tc_i
        //and each data constructor type dt_i
        //and generalize their universes together
        let binders = tcs |> List.map (fun (se, _) ->
            match se.sigel with
            | Sig_inductive_typ(_, _, tps, k, _, _) -> S.null_binder (U.arrow tps <| mk_Total k)
            | _ -> failwith "Impossible")  in
        let binders' = datas |> List.map (fun se -> match se.sigel with
            | Sig_datacon(_, _, t, _, _, _) -> S.null_binder t
            | _ -> failwith "Impossible") in
        let t = U.arrow (binders@binders') (S.mk_Total t_unit) in
        if Env.debug env <| Options.Other "GenUniverses"
        then BU.print1 "@@@@@@Trying to generalize universes in %s\n" (N.term_to_string env t);
        let (uvs, t) = Gen.generalize_universes env t in
        if Env.debug env <| Options.Other "GenUniverses"
        then BU.print2 "@@@@@@Generalized to (%s, %s)\n"
                            (uvs |> List.map (fun u -> (string_of_id u)) |> String.concat ", ")
                            (Print.term_to_string t);
        //Now, (uvs, t) is the generalized type scheme for all the inductives and their data constuctors

        //we have to destruct t, knowing its shape above,
        //and rebuild the Sig_inductive_typ, Sig_datacon etc
        let uvs, t = SS.open_univ_vars uvs t in
        let args, _ = U.arrow_formals t in
        let tc_types, data_types = BU.first_N (List.length binders) args in
        let tcs = List.map2 (fun ({binder_bv=x}) (se, _) -> match se.sigel with
            | Sig_inductive_typ(tc, _, tps, _, mutuals, datas) ->
              let ty = SS.close_univ_vars uvs x.sort in
              let tps, t = match (SS.compress ty).n with
                | Tm_arrow(binders, c) ->
                  let tps, rest = BU.first_N (List.length tps) binders in
                  let t = match rest with
                    | [] -> U.comp_result c
                    | _ -> mk (Tm_arrow(rest, c)) x.sort.pos
                  in
                  tps, t
                | _ -> [], ty
              in
              { se with sigel = Sig_inductive_typ(tc, uvs, tps, t, mutuals, datas) }
            | _ -> failwith "Impossible")
            tc_types tcs
        in

        //4. Instantiate the inductives in each datacon with the generalized universes
        let datas = match uvs with
            | [] -> datas
            | _ ->
             let uvs_universes = uvs |> List.map U_name in
             let tc_insts = tcs |> List.map (function { sigel = Sig_inductive_typ(tc, _, _, _, _, _) } -> (tc, uvs_universes) | _ -> failwith "Impossible") in
             List.map2 (fun ({binder_bv=t}) d ->
                match d.sigel with
                    | Sig_datacon(l, _, _, tc, ntps, mutuals) ->
                        let ty = InstFV.instantiate tc_insts t.sort |> SS.close_univ_vars uvs in
                        { d with sigel = Sig_datacon(l, uvs, ty, tc, ntps, mutuals) }
                    | _ -> failwith "Impossible")
             data_types datas
        in
        tcs, datas


let datacon_typ (data:sigelt) :term =
  match data.sigel with
  | Sig_datacon (_, _, t, _, _, _) -> t
  | _                              -> failwith "Impossible!"

(* private *)
let haseq_suffix = "__uu___haseq"

let is_haseq_lid lid =
  let str = (string_of_lid lid) in
  let len = String.length str in
  let haseq_suffix_len = String.length haseq_suffix in
  len > haseq_suffix_len &&
  String.compare (String.substring str (len - haseq_suffix_len) haseq_suffix_len) haseq_suffix = 0

let get_haseq_axiom_lid lid =
    lid_of_ids (ns_of_lid lid @ [(id_of_text (string_of_id (ident_of_lid lid) ^ haseq_suffix))])

//get the optimized hasEq axiom for this inductive
//the caller is supposed to open the universes, and pass along the universe substitution and universe names
//returns -- lid of the hasEq axiom
//        -- the hasEq axiom for the inductive
//        -- opened parameter binders
//        -- opened index binders
//        -- conjunction of hasEq of the binders
let get_optimized_haseq_axiom (en:env) (ty:sigelt) (usubst:list<subst_elt>) (us:univ_names) :(lident * term * binders * binders * term) =
  let lid, bs, t =
    match ty.sigel with
    | Sig_inductive_typ (lid, _, bs, t, _, _) -> lid, bs, t
    | _                                       -> failwith "Impossible!"
  in

  //apply usubt to bs
  let bs = SS.subst_binders usubst bs in
  //apply usubst to t, but first shift usubst -- is there a way to apply usubst to bs and t together ?
  let t = SS.subst (SS.shift_subst (List.length bs) usubst) t in
  //open t with binders bs
  let bs, t = SS.open_term bs t in
  //get the index binders, if any
  let ibs =
    match (SS.compress t).n with
    | Tm_arrow (ibs, _) -> ibs
    | _                 -> []
  in
  //open the ibs binders
  let ibs = SS.open_binders ibs in
  //term for unapplied inductive type, making a Tm_uinst, otherwise there are unresolved universe variables, may be that's fine ?
  let ind = mk_Tm_uinst (S.fvar lid delta_constant None) (List.map (fun u -> U_name u) us) in
  //apply the bs parameters, bv_to_name ok ? also note that we are copying the qualifiers from the binder, so that implicits remain implicits
  let ind = mk_Tm_app ind (List.map U.arg_of_non_null_binder bs) Range.dummyRange in
  //apply the ibs parameters, bv_to_name ok ? also note that we are copying the qualifiers from the binder, so that implicits remain implicits
  let ind = mk_Tm_app ind (List.map U.arg_of_non_null_binder ibs) Range.dummyRange in
  //haseq of ind
  let haseq_ind = mk_Tm_app U.t_haseq [S.as_arg ind] Range.dummyRange in
  //haseq of all binders in bs, we will add only those binders x:t for which t <: Type u for some fresh universe variable u
  //we want to avoid the case of binders such as (x:nat), as hasEq x is not well-typed
  let bs' = List.filter (fun b ->
    Rel.subtype_nosmt_force en b.binder_bv.sort  (fst (U.type_u ()))
  ) bs in
  let haseq_bs = List.fold_left (fun (t:term) (b:binder) -> U.mk_conj t (mk_Tm_app U.t_haseq [S.as_arg (S.bv_to_name b.binder_bv)] Range.dummyRange)) U.t_true bs' in
  //implication
  let fml = U.mk_imp haseq_bs haseq_ind in
  //attach pattern -- is this the right place ?
  let fml = { fml with n = Tm_meta (fml, Meta_pattern(binders_to_names ibs, [[S.as_arg haseq_ind]])) } in
  //fold right with ibs, close and add a forall b
  //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
  let fml = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app U.tforall [ S.as_arg (U.abs [S.mk_binder b.binder_bv] (SS.close [b] t) None) ] Range.dummyRange) ibs fml in

  //fold right with bs, close and add a forall b
  //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
  let fml = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app U.tforall [ S.as_arg (U.abs [S.mk_binder b.binder_bv] (SS.close [b] t) None) ] Range.dummyRange) bs fml in

  let axiom_lid = get_haseq_axiom_lid lid in
  axiom_lid, fml, bs, ibs, haseq_bs

//soundness condition for this data constructor
//usubst is the universe substitution, and bs are the opened inductive type parameters
let optimized_haseq_soundness_for_data (ty_lid:lident) (data:sigelt) (usubst:list<subst_elt>) (bs:binders) :term =
  let dt = datacon_typ data in
  //apply the universes substitution to dt
  let dt = SS.subst usubst dt in
  match (SS.compress dt).n with
  | Tm_arrow (dbs, _) ->
    //filter out the inductive type parameters, dbs are the remaining binders
    let dbs = snd (List.splitAt (List.length bs) dbs) in
    //substitute bs into dbs
    let dbs = SS.subst_binders (SS.opening_of_binders bs) dbs in
    //open dbs
    let dbs = SS.open_binders dbs in
    //fold on dbs, add haseq of its sort to the guard
    let cond = List.fold_left (fun (t:term) (b:binder) ->
      let haseq_b = mk_Tm_app U.t_haseq [S.as_arg b.binder_bv.sort] Range.dummyRange in
      //label the haseq predicate so that we get a proper error message if the assertion fails
      let sort_range = b.binder_bv.sort.pos in
      let haseq_b = TcUtil.label
                    (BU.format1 "Failed to prove that the type '%s' supports decidable equality because of this argument; add either the 'noeq' or 'unopteq' qualifier" (string_of_lid ty_lid))
                    sort_range
                    haseq_b
      in
      U.mk_conj t haseq_b) U.t_true dbs
    in
    //fold right over dbs and add a forall for each binder in dbs
    List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [S.mk_binder b.binder_bv] (SS.close [b] t) None) ] Range.dummyRange) dbs cond
  | _                -> U.t_true

//this is the folding function for tcs
//all_datas_in_the_bundle are all data constructors, including those of mutually defined inductives
//usubst and us are the universe variables substitution and universe names, we open each type constructor type, and data constructor type with these
//in the type of the accumulator:
    //list<lident * term> is the list of type constructor lidents and formulas of haseq axioms we are accumulating
    //env is the environment in which the next two terms are well-formed (e.g. data constructors are dependent function types, so they may refer to their arguments)
    //term is the lhs of the implication for soundness formula
    //term is the soundness condition derived from all the data constructors of this type
let optimized_haseq_ty (all_datas_in_the_bundle:sigelts) (usubst:list<subst_elt>) (us:list<univ_name>) acc ty =
  let lid =
    match ty.sigel with
    | Sig_inductive_typ (lid, _, _, _, _, _) -> lid
    | _                                      -> failwith "Impossible!"
  in

  let _, en, _, _ = acc in
  let axiom_lid, fml, bs, ibs, haseq_bs = get_optimized_haseq_axiom en ty usubst us in
  //fml is the hasEq axiom for the inductive, bs and ibs are opened binders and index binders,
  //haseq_bs is the conjunction of hasEq of all the binders

  //onto the soundness condition for the above axiom
  //this is the soundness guard
  let guard = U.mk_conj haseq_bs fml in

  //now work on checking the soundness of this formula
  //split acc
  let l_axioms, env, guard', cond' = acc in

  //push universe variables, bs, and ibs, universe variables are pushed at the top level below
  let env = Env.push_binders env bs in
  let env = Env.push_binders env ibs in

  //now generate the soundness condition by iterating over the data constructors
  //get the data constructors for this type
  let t_datas = List.filter (fun s ->
    match s.sigel with
    | Sig_datacon (_, _, _, t_lid, _, _) -> t_lid = lid
    | _                                  -> failwith "Impossible"
  ) all_datas_in_the_bundle in


  //fold over t_datas
  let cond = List.fold_left (fun acc d -> U.mk_conj acc (optimized_haseq_soundness_for_data lid d usubst bs)) U.t_true t_datas in

  //return new accumulator
  l_axioms @ [axiom_lid, fml], env, U.mk_conj guard' guard, U.mk_conj cond' cond


let optimized_haseq_scheme (sig_bndle:sigelt) (tcs:list<sigelt>) (datas:list<sigelt>) (env0:env_t) :list<sigelt> =
  let us, t =
    let ty = List.hd tcs in
    match ty.sigel with
    | Sig_inductive_typ (_, us, _, t, _, _) -> us, t
    | _                                     -> failwith "Impossible!"
  in
  let usubst, us = SS.univ_var_opening us in

  //we need the sigbundle for the inductive to be in the type environment
  let env = Env.push_sigelt env0 sig_bndle in
  env.solver.push "haseq";
  env.solver.encode_sig env sig_bndle;
  let env = Env.push_univ_vars env us in

  let axioms, env, guard, cond = List.fold_left (optimized_haseq_ty datas usubst us) ([], env, U.t_true, U.t_true) tcs in

  let phi =
    let _, t = U.arrow_formals t in
    if U.is_eqtype_no_unrefine t then cond  //AR: if the type is marked as eqtype, you don't get to assume equality of type parameters
    else U.mk_imp guard cond in
  let phi, _ = tc_trivial_guard env phi in
  let _ =
    //is this inline with verify_module ?
    if Env.should_verify env then
      Rel.force_trivial_guard env (Env.guard_of_guard_formula (NonTrivial phi))
    else ()
  in

  //create Sig_assume for the axioms, FIXME: docs?
  let ses = List.fold_left (fun (l:list<sigelt>) (lid, fml) ->
    let fml = SS.close_univ_vars us fml in
    l @ [ { sigel = Sig_assume (lid, us, fml);
            sigquals = [];
            sigrng = Range.dummyRange;
            sigmeta = default_sigmeta;
            sigattrs = [];
            sigopts = None; } ]
  ) [] axioms in

  env.solver.pop "haseq";
  ses

//folding function for t_datas
//usubst is the universe substitution, bs are the opened inductive type parameters
//haseq_ind is the inductive applied to all its bs and ibs
let unoptimized_haseq_data (usubst:list<subst_elt>) (bs:binders) (haseq_ind:term) (mutuals:list<lident>) (acc:term) (data:sigelt) =

  //identify if the type t is a mutually defined type
  //TODO: we now have a get_free_names in Syntax.Free, use that
  let rec is_mutual (t:term) =  //TODO: this should handle more cases
    match (SS.compress t).n with
    | Tm_fvar fv         -> List.existsb (fun lid -> lid_equals lid fv.fv_name.v) mutuals
    | Tm_uinst (t', _)   -> is_mutual t'
    | Tm_refine (bv, t') -> is_mutual bv.sort
    | Tm_app (t', args)  -> if is_mutual t' then true else exists_mutual (List.map fst args)
    | Tm_meta (t', _)    -> is_mutual t'
    | _                  -> false

   and exists_mutual = function
     | [] -> false
     | hd::tl -> is_mutual hd || exists_mutual tl
  in


  let dt = datacon_typ data in
  //apply the universes substitution to dt
  let dt = SS.subst usubst dt in
  match (SS.compress dt).n with
  | Tm_arrow (dbs, _) ->
    //filter out the inductive type parameters, dbs are the remaining binders
    let dbs = snd (List.splitAt (List.length bs) dbs) in
    //substitute bs into dbs
    let dbs = SS.subst_binders (SS.opening_of_binders bs) dbs in
    //open dbs
    let dbs = SS.open_binders dbs in
    //fold on dbs, add haseq of its sort to the guard
    //if the sort is a mutual, guard its hasEq with the hasEq of the current type constructor
    //cond is the conjunct of the hasEq of all the data constructor arguments
    let cond = List.fold_left (fun (t:term) (b:binder) ->
      let sort = b.binder_bv.sort in
      let haseq_sort = mk_Tm_app U.t_haseq [S.as_arg b.binder_bv.sort] Range.dummyRange in
      let haseq_sort = if is_mutual sort then U.mk_imp haseq_ind haseq_sort else haseq_sort in
      U.mk_conj t haseq_sort) U.t_true dbs
    in

            //fold right with dbs, close and add a forall b
                //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
            let cond = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [S.mk_binder b.binder_bv] (SS.close [b] t) None) ] Range.dummyRange) dbs cond in

            //new accumulator is old one /\ cond
            U.mk_conj acc cond
        | _                -> acc

//this is the folding function for tcs
//usubst and us are the universe variables substitution and universe names, we open each type constructor type, and data constructor type with these
//the accumulator is the formula that we are building, for each type constructor, we add a conjunct to it
let unoptimized_haseq_ty (all_datas_in_the_bundle:list<sigelt>) (mutuals:list<lident>) (usubst:list<subst_elt>) (us:list<univ_name>) (acc:term) (ty:sigelt) =
  let lid, bs, t, d_lids =
    match ty.sigel with
    | Sig_inductive_typ (lid, _, bs, t, _, d_lids) -> lid, bs, t, d_lids
    | _                                            -> failwith "Impossible!"
  in

  //apply usubt to bs
  let bs = SS.subst_binders usubst bs in
  //apply usubst to t, but first shift usubst -- is there a way to apply usubst to bs and t together ?
  let t = SS.subst (SS.shift_subst (List.length bs) usubst) t in
  //open t with binders bs
  let bs, t = SS.open_term bs t in
  //get the index binders, if any
  let ibs =
    match (SS.compress t).n with
    | Tm_arrow (ibs, _) -> ibs
    | _                 -> []
  in
  //open the ibs binders
  let ibs = SS.open_binders ibs in
  //term for unapplied inductive type, making a Tm_uinst, otherwise there are unresolved universe variables, may be that's fine ?
  let ind = mk_Tm_uinst (S.fvar lid delta_constant None) (List.map (fun u -> U_name u) us) in
  //apply the bs parameters, bv_to_name ok ? also note that we are copying the qualifiers from the binder, so that implicits remain implicits
  let ind = mk_Tm_app ind (List.map U.arg_of_non_null_binder bs) Range.dummyRange in
  //apply the ibs parameters, bv_to_name ok ? also note that we are copying the qualifiers from the binder, so that implicits remain implicits
  let ind = mk_Tm_app ind (List.map U.arg_of_non_null_binder ibs) Range.dummyRange in
  //haseq of ind applied to all bs and ibs
  let haseq_ind = mk_Tm_app U.t_haseq [S.as_arg ind] Range.dummyRange in


  //filter out data constructors for this type constructor
  let t_datas = List.filter (fun s ->
    match s.sigel with
    | Sig_datacon (_, _, _, t_lid, _, _) -> t_lid = lid
    | _                                  -> failwith "Impossible"
  ) all_datas_in_the_bundle in

  //fold over t_datas
  let data_cond = List.fold_left (unoptimized_haseq_data usubst bs haseq_ind mutuals) U.t_true t_datas in

  //make the implication
  let fml = U.mk_imp data_cond haseq_ind in

  //attach pattern -- is this the right place ?
  let fml = { fml with n = Tm_meta (fml, Meta_pattern(binders_to_names ibs, [[S.as_arg haseq_ind]])) } in

  //fold right with ibs, close and add a forall b
  //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
  let fml = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [S.mk_binder b.binder_bv] (SS.close [b] t) None) ] Range.dummyRange) ibs fml in
  //fold right with bs, close and add a forall b
  //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
  let fml = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [S.mk_binder b.binder_bv] (SS.close [b] t) None) ] Range.dummyRange) bs fml in

  //new accumulator is old accumulator /\ fml
  U.mk_conj acc fml

let unoptimized_haseq_scheme (sig_bndle:sigelt) (tcs:list<sigelt>) (datas:list<sigelt>) (env0:env_t) :list<sigelt> =
  //TODO: perhaps make it a map ?
  let mutuals = List.map (fun ty ->
    match ty.sigel with
    | Sig_inductive_typ (lid, _, _, _, _, _) -> lid
    | _                                      -> failwith "Impossible!") tcs
  in


  let lid, us =
    let ty = List.hd tcs in
    match ty.sigel with
    | Sig_inductive_typ (lid, us, _, _, _, _) -> lid, us
    | _                                       -> failwith "Impossible!"
  in
  let usubst, us = SS.univ_var_opening us in

  let fml = List.fold_left (unoptimized_haseq_ty datas mutuals usubst us) U.t_true tcs in

  let se =  //FIXME: docs?
    { sigel = Sig_assume (get_haseq_axiom_lid lid, us, fml);
              sigquals = [];
              sigrng = Range.dummyRange;
              sigmeta = default_sigmeta;
              sigattrs = [];
              sigopts = None; }

  in
  [se]


//returns: sig bundle, list of type constructors, list of data constructors
let check_inductive_well_typedness (env:env_t) (ses:list<sigelt>) (quals:list<qualifier>) (lids:list<lident>) :(sigelt * list<sigelt> * list<sigelt>) =
    (*  Consider this illustrative example:

         type T (a:Type) : (b:Type) -> Type =
             | C1 : x:a -> y:Type -> T a y
             | C2 : x:a -> z:Type -> w:Type -> T a z

         (1). We elaborate the type of T to
                T :  a:Type(ua) -> b:Type(ub) -> Type(u)

         (2). In a context
              G = a:Type(ua), T: (a:Type(ua) -> b:Type(ub) -> Type(u))
              we elaborate the type of

                C1 to x:a -> y:Type(uy) -> T a y
                C2 to x:a -> z:Type(uz) -> w:Type(uw) -> T a z

              Let the elaborated type of constructor i be of the form
                 xs:ts_i -> ti

              For each constructor i, we check

                 - G, [xs:ts_i]_j |- ts_i_j : Type(u_i_j)
                 - u_i_j <= u
                 - G, [xs:ts_i]   |- ti : Type _
                 - ti is an instance of T a


         (3). We jointly generalize the term

                (a:Type(ua) -> b:Type(ub) -> Type u)
                -> (xs:ts_1 -> t1)
                -> (xs:ts_2 -> t2)
                -> unit

             computing

                (uvs,            (a:Type(ua') -> b:Type(ub') -> Type u')
                                -> (xs:ts_1' -> t1')
                                -> (xs:ts_2' -> t2')
                                -> unit)

             The inductive is generalized to

                T<uvs> (a:Type(ua')) : b:Type(ub') -> Type u'


         (4). We re-typecheck and elaborate the type of each constructor to
              capture the proper instantiations of T

              i.e., we check

                G, T<uvs> : a:Type(ua') -> b:Type(ub') -> Type u', uvs |-
                       xs:ts_i' -> t_i'
                  ~>   xs:ts_i'' -> t_i''


             What we get, in effect, is

             type T<ua, ub, uw> (a:Type(ua)) : Type(ub) -> Type (max ua (ub + 1) (uw + 1)) =
                | C1 : (ua, ub, uw) => a:Type(ua) -> y:Type(ub) -> T<ua,ub,uw> a y
                | C2 : (ua, ub, uw) => a:Type(ua) -> z:Type(ub) -> w:Type(uw) -> T<ua,ub,uw> a z
    *)
  let tys, datas = ses |> List.partition (function { sigel = Sig_inductive_typ _ } -> true | _ -> false) in
  if datas |> BU.for_some (function { sigel = Sig_datacon _ } -> false | _ -> true)
  then raise_error (Errors.Fatal_NonInductiveInMutuallyDefinedType, ("Mutually defined type contains a non-inductive element")) (Env.get_range env);

  //AR: adding this code for the second phase
  //    univs need not be empty
  //    we record whether the universes were already annotated
  //    and later use it to decide if we should generalize
  let univs =
    if List.length tys = 0 then []
    else
      match (List.hd tys).sigel with
      | Sig_inductive_typ (_, uvs, _, _, _, _) -> uvs
      | _ -> failwith "Impossible, can't happen!"
  in

  let env0 = env in

  (* Check each tycon *)
  let env, tcs, g = List.fold_right (fun tc (env, all_tcs, g)  ->
    let env, tc, tc_u, guard = tc_tycon env tc in
    let g' = Rel.universe_inequality S.U_zero tc_u in
    if Env.debug env Options.Low then BU.print1 "Checked inductive: %s\n" (Print.sigelt_to_string tc);
    env, (tc, tc_u)::all_tcs, Env.conj_guard g (Env.conj_guard guard g')
  ) tys (env, [], Env.trivial_guard)
  in

  (* Check each datacon *)
  let datas, g = List.fold_right (fun se (datas, g) ->
    let data, g' = tc_data env tcs se in
    data::datas, Env.conj_guard g g'
  ) datas ([], g)
  in

  (* Generalize their universes if not already annotated *)
  let tcs, datas =
    let tc_universe_vars = List.map snd tcs in
    let g = {g with univ_ineqs=tc_universe_vars, snd (g.univ_ineqs)} in

    if Env.debug env0 <| Options.Other "GenUniverses"
    then BU.print1 "@@@@@@Guard before (possible) generalization: %s\n" (Rel.guard_to_string env g);

    Rel.force_trivial_guard env0 g;
    if List.length univs = 0 then generalize_and_inst_within env0 tcs datas
    else (List.map fst tcs), datas
  in

  let sig_bndle = { sigel = Sig_bundle(tcs@datas, lids);
                    sigquals = quals;
                    sigrng = Env.get_range env0;
                    sigmeta = default_sigmeta;
                    sigattrs = List.collect (fun s -> s.sigattrs) ses;
                    sigopts = None; } in

  (* In any of the tycons had their typed declared using `val`,
     check that the declared and inferred types are compatible *)
  tcs |> List.iter (fun se ->
    match se.sigel with
    | Sig_inductive_typ(l, univs, binders, typ, _, _) ->
      let fail expected inferred =
          raise_error (Errors.Fatal_UnexpectedInductivetype, (BU.format2 "Expected an inductive with type %s; got %s"
                                            (Print.tscheme_to_string expected)
                                            (Print.tscheme_to_string inferred)))
                       se.sigrng
      in
      begin match Env.try_lookup_val_decl env0 l with
            | None -> ()
            | Some (expected_typ, _) ->
              let inferred_typ =
                  let body =
                      match binders with
                      | [] -> typ
                      | _ -> S.mk (Tm_arrow(binders, S.mk_Total typ)) se.sigrng in
                  (univs, body)
              in
              if List.length univs = List.length (fst expected_typ)
              then let _, inferred = Subst.open_univ_vars univs (snd inferred_typ) in
                   let _, expected = Subst.open_univ_vars univs (snd expected_typ) in
                   if Rel.teq_nosmt_force env0 inferred expected
                   then ()
                   else fail expected_typ inferred_typ
              else fail expected_typ inferred_typ
      end
    | _ -> ());
  sig_bndle, tcs, datas


(******************************************************************************)
(*                                                                            *)
(*                Elaboration of the projectors                               *)
(*                                                                            *)
(******************************************************************************)

//for these types we don't generate projectors, discriminators, and hasEq axioms
let early_prims_inductives = [ "empty"; "trivial"; "equals"; "pair"; "sum" ]

let mk_discriminator_and_indexed_projectors iquals                   (* Qualifiers of the envelopping bundle    *)
                                            (attrs:list<attribute>)  (* Attributes of the envelopping bundle    *)
                                            (fvq:fv_qual)            (*                                         *)
                                            (refine_domain:bool)     (* If true, discriminates the projectee    *)
                                            env                      (*                                         *)
                                            (tc:lident)              (* Type constructor name                   *)
                                            (lid:lident)             (* Constructor name                        *)
                                            (uvs:univ_names)         (* Original universe names                 *)
                                            (inductive_tps:binders)  (* Type parameters of the type constructor *)
                                            (indices:binders)        (* Implicit type parameters                *)
                                            (fields:binders)         (* Fields of the constructor               *)
                                            (erasable:bool)          (* Generate ghost discriminators and projectors *)
                                            : list<sigelt> =
    let p = range_of_lid lid in
    let pos q = Syntax.withinfo q p in
    let projectee ptyp = S.gen_bv "projectee" (Some p) ptyp in
    let inst_univs = List.map (fun u -> U_name u) uvs in
    let tps = inductive_tps in //List.map2 (fun (x,_) (_,imp) -> ({x,imp)) implicit_tps inductive_tps in
    let arg_typ =
        let inst_tc = S.mk (Tm_uinst (S.fv_to_tm (S.lid_as_fv tc delta_constant None), inst_univs)) p in
        let args = tps@indices |> List.map U.arg_of_non_null_binder in
        S.mk_Tm_app inst_tc args p
    in
    let unrefined_arg_binder = S.mk_binder (projectee arg_typ) in
    let arg_binder =
        if not refine_domain
        then unrefined_arg_binder //records have only one constructor; no point refining the domain
        else let disc_name = U.mk_discriminator lid in
             let x = S.new_bv (Some p) arg_typ in
             let sort =
                 let disc_fvar = S.fvar (Ident.set_lid_range disc_name p) (Delta_equational_at_level 1) None in
                 U.refine x (U.b2t (S.mk_Tm_app (S.mk_Tm_uinst disc_fvar inst_univs) [as_arg <| S.bv_to_name x] p))
             in
             S.mk_binder ({projectee arg_typ with sort = sort})
    in


    let ntps = List.length tps in
    let all_params = List.map (fun b -> {b with binder_qual=Some S.imp_tag}) tps @ fields in

    let imp_binders = tps @ indices |> List.map (fun b -> {b with binder_qual=Some S.imp_tag}) in

    let early_prims_inductive =
      lid_equals C.prims_lid  (Env.current_module env) &&
      List.existsb (fun s -> s = (string_of_id (ident_of_lid tc))) early_prims_inductives
    in

    let discriminator_ses =
        if fvq <> Data_ctor
        then [] // We do not generate discriminators for record types
        else
            let discriminator_name = U.mk_discriminator lid in
            let no_decl = false in
            let only_decl =
              early_prims_inductive ||
              Options.dont_gen_projectors (string_of_lid (Env.current_module env))
            in
            let quals =
                (* KM : What about Logic ? should it still be there even with an implementation *)
                S.Discriminator lid ::
                (if only_decl then [S.Logic; S.Assumption] else []) @
                //(if only_decl && (not <| env.is_iface || env.admit) then [S.Assumption] else []) @
                List.filter (function S.Inline_for_extraction | S.NoExtract | S.Private -> true | _ -> false ) iquals
            in

            (* Type of the discriminator *)
            let binders = imp_binders@[unrefined_arg_binder] in
            let t =
                let bool_typ =
                  if erasable
                  then S.mk_GTotal U.t_bool
                  else S.mk_Total U.t_bool
                in
                SS.close_univ_vars uvs <| U.arrow binders bool_typ
            in
            let decl = { sigel = Sig_declare_typ(discriminator_name, uvs, t);
                         sigquals = quals;
                         sigrng = range_of_lid discriminator_name;
                         sigmeta = default_sigmeta;
                         sigattrs = attrs;
                         sigopts = None; } in
            if Env.debug env (Options.Other "LogTypes")
            then BU.print1 "Declaration of a discriminator %s\n"  (Print.sigelt_to_string decl);

            if only_decl
            then [decl]
            else
                (* Term of the discriminator *)
                let body =
                    if not refine_domain
                    then U.exp_true_bool   // If we have at most one constructor
                    else
                        let arg_pats = all_params |> List.mapi (fun j ({binder_bv=x;binder_qual=imp}) ->
                            let b = S.is_bqual_implicit imp in
                            if b && j < ntps
                            then pos (Pat_dot_term (S.gen_bv (string_of_id x.ppname) None tun, tun)), b
                            else pos (Pat_wild (S.gen_bv (string_of_id x.ppname) None tun)), b)
                        in
                        let pat_true = pos (S.Pat_cons (S.lid_as_fv lid delta_constant (Some fvq), arg_pats)), None, U.exp_true_bool in
                        let pat_false = pos (Pat_wild (S.new_bv None tun)), None, U.exp_false_bool in
                        let arg_exp = S.bv_to_name unrefined_arg_binder.binder_bv in
                        mk (Tm_match(arg_exp, None, [U.branch pat_true ; U.branch pat_false], None)) p
                in
                let dd = Delta_equational_at_level 1 in
                let imp = U.abs binders body None in
                let lbtyp = if no_decl then t else tun in
                let lb = U.mk_letbinding
                            (Inr (S.lid_as_fv discriminator_name dd None))
                            uvs
                            lbtyp
                            C.effect_Tot_lid
                            (SS.close_univ_vars uvs imp)
                            []
                            Range.dummyRange
                in
                let impl = { sigel = Sig_let((false, [lb]), [lb.lbname |> right |> (fun fv -> fv.fv_name.v)]);
                             sigquals = quals;
                             sigrng = p;
                             sigmeta = default_sigmeta;
                             sigattrs = attrs;
                             sigopts = None; } in
                if Env.debug env (Options.Other "LogTypes")
                then BU.print1 "Implementation of a discriminator %s\n"  (Print.sigelt_to_string impl);
                (* TODO : Are there some cases where we don't want one of these ? *)
                (* If not the declaration is useless, isn't it ?*)
                [decl ; impl]
    in


    let arg_exp = S.bv_to_name arg_binder.binder_bv in
    let binders = imp_binders@[arg_binder] in
    let arg = U.arg_of_non_null_binder arg_binder in

    let subst = fields |> List.mapi (fun i ({binder_bv=a}) ->
            let field_name = U.mk_field_projector_name lid a i in
            let field_proj_tm = mk_Tm_uinst (S.fv_to_tm (S.lid_as_fv field_name (Delta_equational_at_level 1) None)) inst_univs in
            let proj = mk_Tm_app field_proj_tm [arg] p in
            NT(a, proj))
    in

    let projectors_ses =
      fields |> List.mapi (fun i ({binder_bv=x}) ->
          let p = S.range_of_bv x in
          let field_name = U.mk_field_projector_name lid x i in
          let t =
            let result_comp =
              let t = Subst.subst subst x.sort in
              if erasable
              then S.mk_GTotal t
              else S.mk_Total t
            in
            SS.close_univ_vars uvs <| U.arrow binders result_comp
          in
          let only_decl =
            early_prims_inductive ||
            Options.dont_gen_projectors (string_of_lid (Env.current_module env))
          in
          (* KM : Why would we want to prevent a declaration only in this particular case ? *)
          (* TODO : If we don't want the declaration then we need to propagate the right types in the patterns *)
          let no_decl = false (* Syntax.is_type x.sort *) in
          let quals q =
              if only_decl
              then S.Assumption::q
              else q
          in
          let quals =
              let iquals = iquals |> List.filter (function
                  | S.Inline_for_extraction
                  | S.NoExtract
                  | S.Private -> true
                  | _ -> false)
              in
              quals (S.Projector(lid, x.ppname)::iquals) in
          let attrs = (if only_decl then [] else [ U.attr_substitute ])@attrs in
          let decl = { sigel = Sig_declare_typ(field_name, uvs, t);
                       sigquals = quals;
                       sigrng = range_of_lid field_name;
                       sigmeta = default_sigmeta;
                       sigattrs = attrs;
                       sigopts = None; } in
          if Env.debug env (Options.Other "LogTypes")
          then BU.print1 "Declaration of a projector %s\n"  (Print.sigelt_to_string decl);
          if only_decl
          then [decl] //only the signature
          else
              let projection = S.gen_bv (string_of_id x.ppname) None tun in
              let arg_pats = all_params |> List.mapi (fun j ({binder_bv=x;binder_qual=imp}) ->
                  let b = S.is_bqual_implicit imp in
                  if i+ntps=j  //this is the one to project
                  then pos (Pat_var projection), b
                  else if b && j < ntps
                  then pos (Pat_dot_term (S.gen_bv (string_of_id x.ppname) None tun, tun)), b
                  else pos (Pat_wild (S.gen_bv (string_of_id x.ppname) None tun)), b)
              in
              let pat = pos (S.Pat_cons (S.lid_as_fv lid delta_constant (Some fvq), arg_pats)), None, S.bv_to_name projection in
              let body = mk (Tm_match(arg_exp, None, [U.branch pat], None)) p in
              let imp = U.abs binders body None in
              let dd = Delta_equational_at_level 1 in
              let lbtyp = if no_decl then t else tun in
              let lb = {
                  lbname=Inr (S.lid_as_fv field_name dd None);
                  lbunivs=uvs;
                  lbtyp=lbtyp;
                  lbeff=C.effect_Tot_lid;
                  lbdef=SS.close_univ_vars uvs imp;
                  lbattrs=[];
                  lbpos=Range.dummyRange;
              } in
              let impl = { sigel = Sig_let((false, [lb]), [lb.lbname |> right |> (fun fv -> fv.fv_name.v)]);
                           sigquals = quals;
                           sigrng = p;
                           sigmeta = default_sigmeta;
                           sigattrs = attrs;
                           sigopts = None; } in
              if Env.debug env (Options.Other "LogTypes")
              then BU.print1 "Implementation of a projector %s\n"  (Print.sigelt_to_string impl);
              if no_decl then [impl] else [decl;impl]) |> List.flatten
    in
    discriminator_ses @ projectors_ses

let mk_data_operations iquals attrs env tcs se =
  match se.sigel with
  | Sig_datacon(constr_lid, uvs, t, typ_lid, n_typars, _) ->

    let univ_opening, uvs = SS.univ_var_opening uvs in
    let t = SS.subst univ_opening t in
    let formals, _ = U.arrow_formals t in

    let inductive_tps, typ0, should_refine =
        let tps_opt = BU.find_map tcs (fun se ->
            if lid_equals typ_lid (must (U.lid_of_sigelt se))
            then match se.sigel with
                  | Sig_inductive_typ(_, uvs', tps, typ0, _, constrs) ->
                      assert (List.length uvs = List.length uvs') ;
                      Some (tps, typ0, List.length constrs > 1)
                  | _ -> failwith "Impossible"
            else None)
        in
        match tps_opt with
            | Some x -> x
            | None ->
                if lid_equals typ_lid C.exn_lid
                then [], U.ktype0, true
                else raise_error (Errors.Fatal_UnexpectedDataConstructor, "Unexpected data constructor") se.sigrng
    in

    let inductive_tps = SS.subst_binders univ_opening inductive_tps in
    let typ0 = SS.subst  //shift the universe substitution by number of type parameters
      (SS.shift_subst (List.length inductive_tps) univ_opening)
      typ0 in
    let indices, _ = U.arrow_formals typ0 in

    let refine_domain =
        if se.sigquals |> BU.for_some (function RecordConstructor _ -> true | _ -> false)
        then false
        else should_refine
    in

    let fv_qual =
        let filter_records = function
            | RecordConstructor (_, fns) -> Some (Record_ctor(typ_lid, fns))
            | _ -> None
        in match BU.find_map se.sigquals filter_records with
            | None -> Data_ctor
            | Some q -> q
    in

    let fields =
        let imp_tps, fields = BU.first_N n_typars formals in
        let rename = List.map2 (fun ({binder_bv=x}) ({binder_bv=x'}) -> S.NT(x, S.bv_to_name x')) imp_tps inductive_tps in
        SS.subst_binders rename fields
    in
    let erasable = U.has_attribute se.sigattrs FStar.Parser.Const.erasable_attr in
    mk_discriminator_and_indexed_projectors
      iquals attrs fv_qual refine_domain
      env typ_lid constr_lid uvs
      inductive_tps indices fields erasable

  | _ -> []
