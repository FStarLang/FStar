(*
   Copyright 2008-2014 Microsoft Research

   Authors: Nikhil Swamy, Aseem Rastogi

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0
o
   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"
module FStar.TypeChecker.TcInductive
open FStar.All

open FStar
open FStar.Errors
open FStar.TypeChecker
open FStar.TypeChecker.Env
open FStar.Util
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
module BU = FStar.Util //basic util
module U  = FStar.Syntax.Util
module PP = FStar.Syntax.Print

let tc_tycon (env:env_t)     (* environment that contains all mutually defined type constructors *)
             (s:sigelt)      (* a Sig_inductive_type (aka tc) that needs to be type-checked *)
       : env_t          (* environment extended with a refined type for the type-constructor *)
       * sigelt         (* the typed version of s, with universe variables still TBD *)
       * universe       (* universe of the constructed type *)
       * guard_t        (* constraints on implicit variables *)
 = match s.elt with
   | Sig_inductive_typ (tc, uvs, tps, k, mutuals, data, quals) -> //the only valid qual is Private
         assert (uvs = []);
 (*open*)let tps, k = SS.open_term tps k in
         let tps, env_tps, guard_params, us = tc_binders env tps in
         let indices, t = U.arrow_formals k in
         let indices, env', guard_indices, us' = tc_binders env_tps indices in
         let t, guard =
             let t, _, g = tc_tot_or_gtot_term env' t in
             t, Rel.discharge_guard env' (Rel.conj_guard guard_params (Rel.conj_guard guard_indices g)) in
         let k = U.arrow indices (S.mk_Total t) in
         let t_type, u = U.type_u() in
         Rel.force_trivial_guard env' (Rel.teq env' t t_type);

(*close*)let t_tc = U.arrow (tps@indices) (S.mk_Total t) in
         let tps = SS.close_binders tps in
         let k = SS.close tps k in
         let fv_tc = S.lid_as_fv tc Delta_constant None in
         Env.push_let_binding env (Inr fv_tc) ([], t_tc),
         { s with elt = Sig_inductive_typ(tc, [], tps, k, mutuals, data, quals) },
         u,
         guard

    | _ -> failwith "impossible"


(* 2. Checking each datacon *)
let tc_data (env:env_t) (tcs : list<(sigelt * universe)>)
  : sigelt -> sigelt * guard_t =
    fun se -> match se.elt with
    | Sig_datacon(c, _uvs, t, tc_lid, ntps, quals, _mutual_tcs) ->
         assert (_uvs = []);

         let (env, tps, u_tc) = //u_tc is the universe of the inductive that c constructs
            let tps_u_opt = BU.find_map tcs (fun (se, u_tc) ->
                if lid_equals tc_lid (must (U.lid_of_sigelt se))
                then match se.elt with
                     | Sig_inductive_typ(_, _, tps, _, _, _, _) ->
                        let tps = tps |> List.map (fun (x, _) -> (x, Some S.imp_tag)) in
                        let tps = Subst.open_binders tps in
                        Some (Env.push_binders env tps, tps, u_tc)
                     | _ -> failwith "Impossible"
                else None) in
           match tps_u_opt with
            | Some x -> x
            | None ->
              if lid_equals tc_lid Const.exn_lid
              then env, [], U_zero
              else raise (Error("Unexpected data constructor", se.sigrng)) in

         let arguments, result =
            match (SS.compress t).n with
                | Tm_arrow(bs, res) ->
                  //the type of each datacon is already a function with the type params as arguments
                  //need to map the prefix of bs corresponding to params to the tps of the inductive
                  let _, bs' = BU.first_N ntps bs in
                  let t = mk (Tm_arrow(bs', res)) None t.pos in
                  let subst = tps |> List.mapi (fun i (x, _) -> DB(ntps - (1 + i), x)) in
(*open*)          U.arrow_formals (SS.subst subst t)
                | _ -> [], t in

         if Env.debug env Options.Low then BU.print3 "Checking datacon  %s : %s -> %s \n"
                (Print.lid_to_string c)
                (Print.binders_to_string "->" arguments)
                (Print.term_to_string result);


         let arguments, env', us = tc_tparams env arguments in
         let result, res_lcomp = tc_trivial_guard env' result in
         begin match (SS.compress res_lcomp.res_typ).n with
               | Tm_type _ -> ()
               | ty -> raise (Error(BU.format2 "The type of %s is %s, but since this is the result type of a constructor its type should be Type"
                                                (Print.term_to_string result)
                                                (Print.term_to_string (res_lcomp.res_typ)), se.sigrng))
         end;
         let head, _ = U.head_and_args result in
         let _ = match (SS.compress head).n with
            | Tm_fvar fv when S.fv_eq_lid fv tc_lid -> ()
            | _ -> raise (Error(BU.format2 "Expected a constructor of type %s; got %s"
                                        (Print.lid_to_string tc_lid)
                                        (Print.term_to_string head), se.sigrng)) in
         let g =List.fold_left2 (fun g (x, _) u_x ->
                Rel.conj_guard g (Rel.universe_inequality u_x u_tc))
            Rel.trivial_guard
            arguments
            us in

(*close*)let t = U.arrow ((tps |> List.map (fun (x, _) -> (x, Some (Implicit true))))@arguments) (S.mk_Total result) in
                        //NB: the tps are tagged as Implicit inaccessbile arguments of the data constructor
         { se with elt = Sig_datacon(c, [], t, tc_lid, ntps, quals, []) },
         g

   | _ -> failwith "impossible"


(* 3. Generalizing universes and 4. instantiate inductives within the datacons *)
let generalize_and_inst_within (env:env_t) (g:guard_t) (tcs:list<(sigelt * universe)>) (datas:list<sigelt>)
    : list<sigelt> * list<sigelt>
    =   let tc_universe_vars = List.map snd tcs in
        let g = {g with univ_ineqs=tc_universe_vars, snd (g.univ_ineqs)} in

        if Env.debug env <| Options.Other "GenUniverses"
        then BU.print1 "@@@@@@Guard before generalization: %s\n" (Rel.guard_to_string env g);

        Rel.force_trivial_guard env g;
        //We build a single arrow term of the form
        //   tc_1 -> .. -> tc_n -> dt_1 -> .. dt_n -> Tot unit
        //for each type constructor tc_i
        //and each data constructor type dt_i
        //and generalize their universes together
        let binders = tcs |> List.map (fun (se, _) ->
            match se.elt with
            | Sig_inductive_typ(_, _, tps, k, _, _, _) -> S.null_binder (U.arrow tps <| mk_Total k)
            | _ -> failwith "Impossible")  in
        let binders' = datas |> List.map (fun se -> match se.elt with
            | Sig_datacon(_, _, t, _, _, _, _) -> S.null_binder t
            | _ -> failwith "Impossible") in
        let t = U.arrow (binders@binders') (S.mk_Total Common.t_unit) in
        if Env.debug env <| Options.Other "GenUniverses"
        then BU.print1 "@@@@@@Trying to generalize universes in %s\n" (N.term_to_string env t);
        let (uvs, t) = TcUtil.generalize_universes env t in
        if Env.debug env <| Options.Other "GenUniverses"
        then BU.print2 "@@@@@@Generalized to (%s, %s)\n"
                            (uvs |> List.map (fun u -> u.idText) |> String.concat ", ")
                            (Print.term_to_string t);
        //Now, (uvs, t) is the generalized type scheme for all the inductives and their data constuctors

        //we have to destruct t, knowing its shape above,
        //and rebuild the Sig_inductive_typ, Sig_datacon etc
        let uvs, t = SS.open_univ_vars uvs t in
        let args, _ = U.arrow_formals t in
        let tc_types, data_types = BU.first_N (List.length binders) args in
        let tcs = List.map2 (fun (x, _) (se, _) -> match se.elt with
            | Sig_inductive_typ(tc, _, tps, _, mutuals, datas, quals) ->
              let ty = SS.close_univ_vars uvs x.sort in
              let tps, t = match (SS.compress ty).n with
                | Tm_arrow(binders, c) ->
                  let tps, rest = BU.first_N (List.length tps) binders in
                  let t = match rest with
                    | [] -> U.comp_result c
                    | _ -> mk (Tm_arrow(rest, c)) !x.sort.tk x.sort.pos
                  in
                  tps, t
                | _ -> [], ty
              in
              { se with elt = Sig_inductive_typ(tc, uvs, tps, t, mutuals, datas, quals) }
            | _ -> failwith "Impossible")
            tc_types tcs
        in

        //4. Instantiate the inductives in each datacon with the generalized universes
        let datas = match uvs with
            | [] -> datas
            | _ ->
             let uvs_universes = uvs |> List.map U_name in
             let tc_insts = tcs |> List.map (function { elt = Sig_inductive_typ(tc, _, _, _, _, _, _) } -> (tc, uvs_universes) | _ -> failwith "Impossible") in
             List.map2 (fun (t, _) d ->
                match d.elt with
                    | Sig_datacon(l, _, _, tc, ntps, quals, mutuals) ->
                        let ty = InstFV.instantiate tc_insts t.sort |> SS.close_univ_vars uvs in
                        { d with elt = Sig_datacon(l, uvs, ty, tc, ntps, quals, mutuals) }
                    | _ -> failwith "Impossible")
             data_types datas
        in
        tcs, datas


let debug_log (env:env_t) (s:string) :unit = if Env.debug env <| Options.Other "Positivity" then BU.print_string ("Positivity::" ^ s ^ "\n") else ()

//return true if ty occurs in the term
let ty_occurs_in (ty_lid:lident) (t:term) :bool = FStar.Util.set_mem ty_lid (Free.fvars t)

//this function is called during the positivity check, when we have a binder type that is a Tm_app, and t is the head node of Tm_app
//it tries to get fvar from this t, since the type is already normalized, other cases should have been handled
let try_get_fv (t:term) :(fv * universes) =
match (SS.compress t).n with
| Tm_fvar fv       -> fv, []
| Tm_uinst (t, us) ->
    (match t.n with
    | Tm_fvar fv   -> fv, us
    | _            -> failwith "Node is a Tm_uinst, but Tm_uinst is not an fvar")
| _                -> failwith "Node is not an fvar or a Tm_uinst"

type unfolded_memo_elt = list<(lident * args)>
type unfolded_memo_t = ref<unfolded_memo_elt>

//check if ilid applied to args has already been unfolded
//in the memo table we only keep the type parameters, not indexes, but the passed args also contain indexes
//so, once we have confirmed that the ilid is same, we will split the args list before checking equality of each argument
let already_unfolded (ilid:lident) (arrghs:args) (unfolded:unfolded_memo_t) (env:env_t) :bool =
  List.existsML (fun (lid, l) ->
    Ident.lid_equals lid ilid &&
      (let args = fst (List.splitAt (List.length l) arrghs) in
       List.fold_left2 (fun b a a' -> b && Rel.teq_nosmt env (fst a) (fst a')) true args l)
  ) !unfolded

//check if ty_lid occurs strictly positively in some binder type btype
let rec ty_strictly_positive_in_type (ty_lid:lident) (btype:term) (unfolded:unfolded_memo_t) (env:env_t) :bool =
  debug_log env ("Checking strict positivity in type: " ^ (PP.term_to_string btype));
  //normalize the type to unfold any type abbreviations, TODO: what steps?
  let btype = N.normalize [N.Beta; N.Eager_unfolding; N.UnfoldUntil Delta_constant; N.Iota; N.Zeta; N.AllowUnboundUniverses] env btype in
  debug_log env ("Checking strict positivity in type, after normalization: " ^ (PP.term_to_string btype));
  not (ty_occurs_in ty_lid btype) ||  //true if ty does not occur in btype
    (debug_log env ("ty does occur in this type, pressing ahead");
     match (SS.compress btype).n with
     | Tm_app (t, args) ->  //the binder type is an application
       //get the head node fv, try_get_fv would fail if it's not an fv
       let fv, us = try_get_fv t in
       //if it's same as ty_lid, then check that ty_lid does not occur in the arguments
       if Ident.lid_equals fv.fv_name.v ty_lid then
         let _ = debug_log env ("Checking strict positivity in the Tm_app node where head lid is ty itself, checking that ty does not occur in the arguments") in
         List.for_all (fun (t, _) -> not (ty_occurs_in ty_lid t)) args
         //else it must be another inductive type, and we would check nested positivity, ty_nested_positive fails if fv is not another inductive
         //that case could arise when, for example, it's a type constructor that we could not unfold in normalization
       else
         let _ = debug_log env ("Checking strict positivity in the Tm_app node, head lid is not ty, so checking nested positivity") in
         ty_nested_positive_in_inductive ty_lid fv.fv_name.v us args unfolded env
     | Tm_arrow (sbs, c) ->  //binder type is an arrow type
       debug_log env ("Checking strict positivity in Tm_arrow");
       if not (is_pure_or_ghost_comp c) then
         let _ = debug_log env ("Checking strict positivity , the arrow is impure, so return true") in
         true
       else
         let _ = debug_log env ("Checking struict positivity, Pure arrow, checking that ty does not occur in the binders, and that it is strictly positive in the return type") in
         List.for_all (fun (b, _) -> not (ty_occurs_in ty_lid b.sort)) sbs &&  //ty must not occur on the left of any arrow
           (let _, return_type = SS.open_term sbs (FStar.Syntax.Util.comp_result c) in  //and it must occur strictly positive in the result type
            ty_strictly_positive_in_type ty_lid return_type unfolded (push_binders env sbs)) //TODO: do we need to compress c, if so how?
     | Tm_fvar _ ->
       debug_log env ("Checking strict positivity in an fvar, return true");
       true  //if it's just an fvar, should be fine
     | Tm_type _ ->  //TODO: actually we should not even reach here, it should already be covered by ty_occurs_in check at the beginning
       debug_log env ("Checking strict positivity in an Tm_type, return true");
       true  //if it's just a Type(u), should be fine
     | Tm_uinst (t, _) ->
       debug_log env ("Checking strict positivity in an Tm_uinst, recur on the term inside (mostly it should be the same inductive)");
       ty_strictly_positive_in_type ty_lid t unfolded env
     | Tm_refine (bv, _) ->
       debug_log env ("Checking strict positivity in an Tm_refine, recur in the bv sort)");
       ty_strictly_positive_in_type ty_lid bv.sort unfolded env
     | Tm_match (_, branches) ->
       debug_log env ("Checking strict positivity in an Tm_match, recur in the branches)");
       List.for_all (fun (p, _, t) ->
         let bs = List.map mk_binder (pat_bvs p) in
         let bs, t = SS.open_term bs t in
         ty_strictly_positive_in_type ty_lid t unfolded (push_binders env bs)
       ) branches
     | Tm_ascribed (t, _, _) ->
       debug_log env ("Checking strict positivity in an Tm_ascribed, recur)");
       ty_strictly_positive_in_type ty_lid t unfolded env
     | _ ->
       debug_log env ("Checking strict positivity, unexpected tag: " ^ (PP.tag_of_term btype) ^ " and term: " ^ (PP.term_to_string btype));
       false)  //remaining cases, will handle as they come up

//some binder of some data constructor is an application of ilid to the args
//ilid may not be an inductive, in which case we simply return false
//us are the universes that the inductive ilid's data constructors can be instantiated with if needed, these us come from the application of ilid that called this function
//TODO: change the name of the function to reflect this behavior
and ty_nested_positive_in_inductive (ty_lid:lident) (ilid:lident) (us:universes) (args:args) (unfolded:unfolded_memo_t) (env:env_t) :bool =
  debug_log env ("Checking nested positivity in the inductive " ^ ilid.str ^ " applied to arguments: " ^ (PP.args_to_string args));
  let b, idatas = datacons_of_typ env ilid in
  //if ilid is not an inductive, return false
  if not b then
    let _ = debug_log env ("Checking nested positivity, not an inductive, return false") in
    false
  //if ilid has already been unfolded with same arguments, return true
  else
    if already_unfolded ilid args unfolded env then
      let _ = debug_log env ("Checking nested positivity, we have already unfolded this inductive with these args") in
      true
    else
      //TODO: is there a better way to get the number of binders of the inductive?
      //note that num_ibs gives us only the type parameters, and not inductives, which is what we need since we will substitute them in the data constructor type
      let num_ibs = num_inductive_ty_params env ilid in
      debug_log env ("Checking nested positivity, number of type parameters is " ^ (string_of_int num_ibs) ^ ", also adding to the memo table");
      //update the memo table with the inductive name and the args, note we keep only the parameters and not indices
      unfolded := !unfolded @ [ilid, fst (List.splitAt num_ibs args)];
      List.for_all (fun d -> ty_nested_positive_in_dlid ty_lid d ilid us args num_ibs unfolded env) idatas

//dlid is a data constructor of ilid, args are the arguments of the ilid application, num_ibs is the # of type parameters of ilid
//us are the universes, see the exaplanation on ty_nested_positive_in_inductive
and ty_nested_positive_in_dlid (ty_lid:lident) (dlid:lident) (ilid:lident) (us:universes) (args:args) (num_ibs:int) (unfolded:unfolded_memo_t) (env:env_t) :bool =
  debug_log env ("Checking nested positivity in data constructor " ^ dlid.str ^ " of the inductive " ^ ilid.str);
  //get the type of the data constructor
  let univ_unif_vars, dt = lookup_datacon env dlid in
  //lookup_datacon instantiates the universes of dlid with unification variables
  //we should unify the universe variables with us, us are the universes that the ilid fvar was instantiated with
  (List.iter2 (fun u' u -> match u' with
     | U_unif u'' -> Unionfind.change u'' (Some u)
     | _          -> failwith "Impossible! Expected universe unification variables") univ_unif_vars us);

  //normalize it, TODO: as before steps?
  let dt = N.normalize [N.Beta; N.Eager_unfolding; N.UnfoldUntil Delta_constant; N.Iota; N.Zeta; N.AllowUnboundUniverses] env dt in

  debug_log env ("Checking nested positivity in the data constructor type: " ^ (PP.term_to_string dt));
  match (SS.compress dt).n with
  | Tm_arrow (dbs, c) ->  //if the data construtor type is an arrow, we need to substitute the args for type parameters of ilid
    //so ibs are the type parameters of inductive, that we would substitute with args, dbs are remaining binders of the data constructor
    debug_log env ("Checked nested positivity in Tm_arrow data constructor type");
    let ibs, dbs = List.splitAt num_ibs dbs in
    //open ibs
    let ibs = SS.open_binders ibs in
    //substitute the opening of ibs in dbs, and in c
    let dbs = SS.subst_binders (SS.opening_of_binders ibs) dbs in
    let c = SS.subst_comp (SS.opening_of_binders ibs) c in
    //get the number of arguments that cover the type parameters num_ibs, these are what we will substitute, remaining ones are the indexes that we leave
    let args, _ = List.splitAt num_ibs args in
    //form the substitution, it's a name -> term substitution list
    let subst = List.fold_left2 (fun subst ib arg -> subst @ [NT (fst ib, fst arg)]) [] ibs args in
    //substitute into the dbs and the computation type c
    let dbs = SS.subst_binders subst dbs in
    let c = SS.subst_comp (SS.shift_subst (List.length dbs) subst) c in

    debug_log env ("Checking nested positivity in the unfolded data constructor binders as: " ^ (PP.binders_to_string "; " dbs) ^ ", and c: " ^ (PP.comp_to_string c));
    ty_nested_positive_in_type ty_lid (Tm_arrow (dbs, c)) ilid num_ibs unfolded env
  | _ ->
    debug_log env ("Checking nested positivity in the data constructor type that is not an arrow");
    ty_nested_positive_in_type ty_lid (SS.compress dt).n ilid num_ibs unfolded env  //in this case, we don't have anything to substitute, simply check

//t is some data constructor type of ilid, after ilid type parameters have been substituted
and ty_nested_positive_in_type (ty_lid:lident) (t:term') (ilid:lident) (num_ibs:int) (unfolded:unfolded_memo_t) (env:env_t) :bool =
  match t with
  | Tm_app (t, args) ->
    //if it's an application node, it must be ilid directly
    debug_log env ("Checking nested positivity in an Tm_app node, which is expected to be the ilid itself");
    let fv, _ = try_get_fv t in
    if Ident.lid_equals fv.fv_name.v ilid then true  //TODO: in this case Coq manual says we should check for indexes
    else failwith "Impossible, expected the type to be ilid"
  | Tm_arrow (sbs, c) ->
    //if it's an arrow type, we want to check that ty occurs strictly positive in the sort of every binder
    //TODO: do something with c also?
    debug_log env ("Checking nested positivity in an Tm_arrow node, with binders as: " ^ (PP.binders_to_string "; " sbs));
    let b, _ =
    List.fold_left (fun (r, env) b ->
        if not r then r, env  //we have already seen a problematic binder
        else ty_strictly_positive_in_type ty_lid (fst b).sort unfolded env, push_binders env [b]
    ) (true, env) sbs
    in
    b
| _ -> failwith "Nested positive check, unhandled case"


//ty_bs are the opended type parameters of the inductive, and ty_usubst is the universe substitution, again from the ty_lid type
let ty_positive_in_datacon (ty_lid:lident) (dlid:lident) (ty_bs:binders) (us:universes) (unfolded:unfolded_memo_t) (env:env) :bool =
  //get the type of the data constructor
  let univ_unif_vars, dt = lookup_datacon env dlid in
  //lookup_datacon instantiates the universes of dlid with unification variables
  //we should unify the universe variables with us, us are the universes that the ilid fvar was instantiated with
  (List.iter2 (fun u' u -> match u' with
     | U_unif u'' -> Unionfind.change u'' (Some u)
     | _          -> failwith "Impossible! Expected universe unification variables") univ_unif_vars us);

  debug_log env ("Checking data constructor type: " ^ (PP.term_to_string dt));
  match (SS.compress dt).n with
  | Tm_fvar _ ->
    debug_log env ("Data constructor type is simply an fvar, returning true");
    true  //if the dataconstructor type is simply an fvar, should be an inductive with no params, no indexes, and no binders in data constructor type
  | Tm_arrow (dbs, _) ->  //TODO: we should check the computation type is not of the form t (t a), but then typechecker already rejects this type
    //filter out the inductive type parameters, dbs are the remaining binders
    let dbs = snd (List.splitAt (List.length ty_bs) dbs) in
    //open dbs with ty_bs opening
    let dbs = SS.subst_binders (SS.opening_of_binders ty_bs) dbs in
    //open dbs
    let dbs = SS.open_binders dbs in
    //check that ty occurs strictly positively in each binder sort
    debug_log env ("Data constructor type is an arrow type, so checking strict positivity in " ^ (string_of_int (List.length dbs)) ^ " binders");
    let b, _ =
      List.fold_left (fun (r, env) b ->
        if not r then r, env  //if we have already found some binder that does not satisfy the condition, short circuit
        else ty_strictly_positive_in_type ty_lid (fst b).sort unfolded env, push_binders env [b]  //push the binder in the environment, we do some normalization, so might be better to keep env good
      ) (true, env) dbs
    in
    b
  | Tm_app (_, _) ->
    debug_log env ("Data constructor type is a Tm_app, so returning true");
    true  //if the data constructor type is a simple app, it must be t ..., and we already don't allow t (t ..), so nothing to check here
    | _ -> failwith "Unexpected data constructor type when checking positivity"

let check_positivity (ty:sigelt) (env:env_t) :bool =
  //memo table, memoizes the Tm_app nodes for inductives that we have already unfolded
  let unfolded_inductives = BU.mk_ref [] in
  
  //ty_bs are the parameters of ty, it does not include the indexes (also indexes are not parameters of data constructor types, inductive type parameters are)
  let ty_lid, ty_us, ty_bs =
    match ty.elt with
    | Sig_inductive_typ (lid, us, bs, _, _, _, _) -> lid, us, bs
    | _                                           -> failwith "Impossible!"
  in
  
  //open the universe variables, we will use these universe names for data constructors also later on
  let ty_usubst, ty_us = SS.univ_var_opening ty_us in
  //push the universe names in the env
  let env = push_univ_vars env ty_us in
  //also push the parameters
  let env = push_binders env ty_bs in

  //apply ty_usubst to ty_bs
  let ty_bs = SS.subst_binders ty_usubst ty_bs in
  let ty_bs = SS.open_binders ty_bs in

  List.for_all (fun d -> ty_positive_in_datacon ty_lid d ty_bs (List.map (fun s -> U_name s) ty_us) unfolded_inductives env) (snd (datacons_of_typ env ty_lid))

let datacon_typ (data:sigelt) :term =
  match data.elt with
  | Sig_datacon (_, _, t, _, _, _, _) -> t
  | _                                 -> failwith "Impossible!"

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
      let haseq_b = mk_Tm_app U.t_haseq [S.as_arg (fst b).sort] None Range.dummyRange in
      //label the haseq predicate so that we get a proper error message if the assertion fails
      let sort_range = (fst b).sort.pos in
      let haseq_b = TcUtil.label
                    (BU.format1 "Failed to prove that the type '%s' supports decidable equality because of this argument; add the 'noeq' qualifier" ty_lid.str)
                    sort_range
                    haseq_b
      in
      U.mk_conj t haseq_b) U.t_true dbs
    in
    //fold right over dbs and add a forall for each binder in dbs
    List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [(fst b, None)] (SS.close [b] t) None) ] None Range.dummyRange) dbs cond
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
  let lid, bs, t, d_lids =
    match ty.elt with
    | Sig_inductive_typ (lid, _, bs, t, _, d_lids, _) -> lid, bs, t, d_lids
    | _                                               -> failwith "Impossible!"
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
  let ind = mk_Tm_uinst (S.fvar lid Delta_constant None) (List.map (fun u -> U_name u) us) in
  //apply the bs parameters, bv_to_name ok ? also note that we are copying the qualifiers from the binder, so that implicits remain implicits
  let ind = mk_Tm_app ind (List.map (fun (bv, aq) -> S.bv_to_name bv, aq) bs) None Range.dummyRange in
  //apply the ibs parameters, bv_to_name ok ? also note that we are copying the qualifiers from the binder, so that implicits remain implicits
  let ind = mk_Tm_app ind (List.map (fun (bv, aq) -> S.bv_to_name bv, aq) ibs) None Range.dummyRange in
  //haseq of ind
  let haseq_ind = mk_Tm_app U.t_haseq [S.as_arg ind] None Range.dummyRange in
  //haseq of all binders in bs, we will add only those binders x:t for which t <: Type u for some fresh universe variable u
  //we want to avoid the case of binders such as (x:nat), as hasEq x is not well-typed
  let bs' = List.filter (fun b ->
    let _, en, _, _ = acc in
    //false means don't use SMT solver
    let opt = Rel.try_subtype' en (fst b).sort  (fst (type_u ())) false in
    //is this criteria for success/failure ok ?
    match opt with
    | None   -> false
    | Some _ -> true
  ) bs in
  let haseq_bs = List.fold_left (fun (t:term) (b:binder) -> U.mk_conj t (mk_Tm_app U.t_haseq [S.as_arg (S.bv_to_name (fst b))] None Range.dummyRange)) U.t_true bs' in
  //implication
  let fml = U.mk_imp haseq_bs haseq_ind in
  //attach pattern -- is this the right place ?
  let fml = { fml with n = Tm_meta (fml, Meta_pattern [[S.as_arg haseq_ind]]) } in
  //fold right with ibs, close and add a forall b
  //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
  let fml = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [(fst b, None)] (SS.close [b] t) None) ] None Range.dummyRange) ibs fml in
  //fold right with bs, close and add a forall b
  //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
  let fml = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [(fst b, None)] (SS.close [b] t) None) ] None Range.dummyRange) bs fml in
  //so now fml is the haseq axiom we want to generate

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
    match s.elt with
    | Sig_datacon (_, _, _, t_lid, _, _, _) -> t_lid = lid
    | _                                     -> failwith "Impossible"
  ) all_datas_in_the_bundle in


  //fold over t_datas
  let cond = List.fold_left (fun acc d -> U.mk_conj acc (optimized_haseq_soundness_for_data lid d usubst bs)) U.t_true t_datas in

  //return new accumulator
  let axiom_lid = lid_of_ids (lid.ns @ [(id_of_text (lid.ident.idText ^ "_haseq"))]) in
  l_axioms @ [axiom_lid, fml], env, U.mk_conj guard' guard, U.mk_conj cond' cond


let optimized_haseq_scheme (sig_bndle:sigelt) (tcs:list<sigelt>) (datas:list<sigelt>) (env0:env_t) (tc_assume:(env_t -> lident -> formula -> list<qualifier> -> Range.range -> sigelt)) :list<sigelt> =
  let us =
    let ty = List.hd tcs in
    match ty.elt with
    | Sig_inductive_typ (_, us, _, _, _, _, _) -> us
    | _                                        -> failwith "Impossible!"
  in
  let usubst, us = SS.univ_var_opening us in

  //we need the sigbundle for the inductive to be in the type environment
  let env = Env.push_sigelt env0 sig_bndle in
  env.solver.push "haseq";
  env.solver.encode_sig env sig_bndle;
  let env = Env.push_univ_vars env us in

  let axioms, env, guard, cond = List.fold_left (optimized_haseq_ty datas usubst us) ([], env, U.t_true, U.t_true) tcs in

  let phi = U.mk_imp guard cond in
  let phi, _ = tc_trivial_guard env phi in
  let _ =
    //is this inline with verify_module ?
    if Env.should_verify env then
      Rel.force_trivial_guard env (Rel.guard_of_guard_formula (NonTrivial phi))
    else ()
  in

  //create Sig_assume for the axioms
  let ses = List.fold_left (fun (l:list<sigelt>) (lid, fml) ->
    let se = tc_assume env lid fml [] Range.dummyRange in
    //se has free universe variables in it, TODO: fix it by making Sig_assume a type scheme
    l @ [se]
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
      let sort = (fst b).sort in
      let haseq_sort = mk_Tm_app U.t_haseq [S.as_arg (fst b).sort] None Range.dummyRange in
      let haseq_sort = if is_mutual sort then U.mk_imp haseq_ind haseq_sort else haseq_sort in
      U.mk_conj t haseq_sort) U.t_true dbs
    in

            //fold right with dbs, close and add a forall b
	        //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
            let cond = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [(fst b, None)] (SS.close [b] t) None) ] None Range.dummyRange) dbs cond in

            //new accumulator is old one /\ cond
            U.mk_conj acc cond
        | _                -> acc

//this is the folding function for tcs
//usubst and us are the universe variables substitution and universe names, we open each type constructor type, and data constructor type with these
//the accumulator is the formula that we are building, for each type constructor, we add a conjunct to it
let unoptimized_haseq_ty (all_datas_in_the_bundle:list<sigelt>) (mutuals:list<lident>) (usubst:list<subst_elt>) (us:list<univ_name>) (acc:term) (ty:sigelt) =
  let lid, bs, t, d_lids =
    match ty.elt with
    | Sig_inductive_typ (lid, _, bs, t, _, d_lids, _) -> lid, bs, t, d_lids
    | _                                               -> failwith "Impossible!"
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
  let ind = mk_Tm_uinst (S.fvar lid Delta_constant None) (List.map (fun u -> U_name u) us) in
  //apply the bs parameters, bv_to_name ok ? also note that we are copying the qualifiers from the binder, so that implicits remain implicits
  let ind = mk_Tm_app ind (List.map (fun (bv, aq) -> S.bv_to_name bv, aq) bs) None Range.dummyRange in
  //apply the ibs parameters, bv_to_name ok ? also note that we are copying the qualifiers from the binder, so that implicits remain implicits
  let ind = mk_Tm_app ind (List.map (fun (bv, aq) -> S.bv_to_name bv, aq) ibs) None Range.dummyRange in
  //haseq of ind applied to all bs and ibs
  let haseq_ind = mk_Tm_app U.t_haseq [S.as_arg ind] None Range.dummyRange in


  //filter out data constructors for this type constructor
  let t_datas = List.filter (fun s ->
    match s.elt with
    | Sig_datacon (_, _, _, t_lid, _, _, _) -> t_lid = lid
    | _                                     -> failwith "Impossible"
  ) all_datas_in_the_bundle in

  //fold over t_datas
  let data_cond = List.fold_left (unoptimized_haseq_data usubst bs haseq_ind mutuals) U.t_true t_datas in

  //make the implication
  let fml = U.mk_imp data_cond haseq_ind in

  //attach pattern -- is this the right place ?
  let fml = { fml with n = Tm_meta (fml, Meta_pattern [[S.as_arg haseq_ind]]) } in

  //fold right with ibs, close and add a forall b
  //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
  let fml = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [(fst b, None)] (SS.close [b] t) None) ] None Range.dummyRange) ibs fml in
  //fold right with bs, close and add a forall b
  //we are setting the qualifier of the binder to None explicitly, we don't want to make forall binder implicit etc. ?
  let fml = List.fold_right (fun (b:binder) (t:term) -> mk_Tm_app tforall [ S.as_arg (U.abs [(fst b, None)] (SS.close [b] t) None) ] None Range.dummyRange) bs fml in

  //new accumulator is old accumulator /\ fml
  U.mk_conj acc fml

let unoptimized_haseq_scheme (sig_bndle:sigelt) (tcs:list<sigelt>) (datas:list<sigelt>) (env0:env_t) (tc_assume:(env_t -> lident -> formula -> list<qualifier> -> Range.range -> sigelt)) :list<sigelt> =
  //TODO: perhaps make it a map ?
  let mutuals = List.map (fun ty ->
    match ty.elt with
    | Sig_inductive_typ (lid, _, _, _, _, _, _) -> lid
    | _                                         -> failwith "Impossible!") tcs
  in


  let lid, us =
    let ty = List.hd tcs in
    match ty.elt with
    | Sig_inductive_typ (lid, us, _, _, _, _, _) -> lid, us
    | _                                        -> failwith "Impossible!"
  in
  let usubst, us = SS.univ_var_opening us in

  let fml = List.fold_left (unoptimized_haseq_ty datas mutuals usubst us) U.t_true tcs in

  let env = Env.push_sigelt env0 sig_bndle in
  env.solver.push "haseq";

  env.solver.encode_sig env sig_bndle;
  let env = Env.push_univ_vars env us in
  let se = tc_assume env (lid_of_ids (lid.ns @ [(id_of_text (lid.ident.idText ^ "_haseq"))])) fml [] Range.dummyRange in

  env.solver.pop "haseq";
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
  let tys, datas = ses |> List.partition (function { elt = Sig_inductive_typ _ } -> true | _ -> false) in
  if datas |> BU.for_some (function { elt = Sig_datacon _ } -> false | _ -> true)
  then raise (Error("Mutually defined type contains a non-inductive element", Env.get_range env));
  let env0 = env in

  (* Check each tycon *)
  let env, tcs, g = List.fold_right (fun tc (env, all_tcs, g)  ->
    let env, tc, tc_u, guard = tc_tycon env tc in
    let g' = Rel.universe_inequality S.U_zero tc_u in
    if Env.debug env Options.Low then BU.print1 "Checked inductive: %s\n" (Print.sigelt_to_string tc);
    env, (tc, tc_u)::all_tcs, Rel.conj_guard g (Rel.conj_guard guard g')
  ) tys (env, [], Rel.trivial_guard)
  in

  (* Check each datacon *)
  let datas, g = List.fold_right (fun se (datas, g) ->
    let data, g' = tc_data env tcs se in
    data::datas, Rel.conj_guard g g'
  ) datas ([], g)
  in

  (* Generalize their universes *)
  let tcs, datas = generalize_and_inst_within env0 g tcs datas in

  let sig_bndle = { elt = Sig_bundle(tcs@datas, quals, lids); sigrng = Env.get_range env0; doc = None } in // FIXME: Doc
  sig_bndle, tcs, datas
