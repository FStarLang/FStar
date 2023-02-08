(*
   Copyright 2008-2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: A. Rastogi, N. Swamy
*)

module FStar.TypeChecker.Positivity
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.TypeChecker.Env
open FStar.Syntax
open FStar.Syntax.Syntax
open FStar.Ident
open FStar.Errors
open FStar.List.Tot
module S = FStar.Syntax.Syntax
module SS = FStar.Syntax.Subst
module BU = FStar.Compiler.Util
module U = FStar.Syntax.Util
module N = FStar.TypeChecker.Normalize
module L = FStar.Compiler.List
module C = FStar.Parser.Const

let normalize env t =
    N.normalize [Env.Beta;
                 Env.HNF;
                 Env.Weak;
                 Env.Iota;
                 Env.Exclude Env.Zeta;
                 Env.UnfoldUntil delta_constant]
                 env
                 t

let debug_positivity (env:env_t) (msg:unit -> string) : unit =
  if Env.debug env <| Options.Other "Positivity"
  then BU.print_string ("Positivity::" ^ msg () ^ "\n")

(* Given a data constructor d : dt
   and parameters to an instance of d's constructed type,
   instantiate the arguments of d corresponding to the type parameters
   with all_params *)
let apply_datacon_arrow (dlid:lident) (dt:term) (all_params:list arg)
  : term 
  = let rec aux t args =
        match (SS.compress t).n, args with
        | _, [] -> U.canon_arrow t
        | Tm_arrow(b::bs, c), a::args ->
          let tail = 
            match bs with
            | [] -> U.comp_result c
            | _ -> S.mk (Tm_arrow(bs, c)) t.pos
          in
          let b, tail = SS.open_term_1 b tail in
          let tail = SS.subst [NT(b.binder_bv, fst a)] tail in
          aux tail args
        | _ ->
          raise_error 
             (Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
              BU.format3 "Unexpected application of type parameters %s to a data constructor %s : %s"
                         (Print.args_to_string all_params)
                         (Ident.string_of_lid dlid)
                         (Print.term_to_string dt))
             (Ident.range_of_lid dlid)
    in
    aux dt all_params

(* Checks if ty_lid appears as an fvar in t *)
let ty_occurs_in (ty_lid:lident)
                 (t:term)
  : bool
  = FStar.Compiler.Util.set_mem ty_lid (Free.fvars t)

(* Checks is `t` is a name or fv and returns it, if so. *)
let rec term_as_fv_or_name (t:term) 
  : option (either (fv * universes) bv)
  = match (SS.compress t).n with
    | Tm_name x -> 
      Some (Inr x)
      
    | Tm_fvar fv ->
      Some (Inl (fv, []))
      
    | Tm_uinst (t, us) ->
      (match (SS.compress t).n with
       | Tm_fvar fv -> Some (Inl (fv, us))
       | _ -> failwith "term_as_fv_or_name: impossible non fvar in uinst")
      
    | Tm_ascribed (t, _, _) -> 
      term_as_fv_or_name t
      
    | _ -> None

(* unfolded_memo_t: This is a key data structure in the 
   strict positivity check for inductive types.

   Consider, for example, checking the positivity of

   type t =
     | T : list t -> t

   We look at every constructor of the instantiation `list t` 
   and check that it is positive, after recording in the memo-table
   that `list t` is positive.
   
   When we reach the `tl` field of `Cons : hd:t -> tl:list t -> list t`,
   we find `list t` in the memo-table and avoid infinitely recursing
   on it.
*)
//A type name, the instantiation, and the number of arguments
type unfolded_memo_elt = list (lident & args & int) 
type unfolded_memo_t = ref unfolded_memo_elt



(* Check if `ilid args` is in the memo table.
   Note: the memo table only constains instantiations of ilid to its parameters
   whereas args also includes the indexes. So, we take the prefix of args
*)
let already_unfolded (ilid:lident)
                     (args:args)
                     (unfolded:unfolded_memo_t)
                     (env:env_t)
  : bool
  = List.existsML 
      (fun (lid, l, n) ->
         Ident.lid_equals lid ilid &&
         List.length args >= n &&
         (let args = fst (L.splitAt n args) in
          List.fold_left2 
            (fun b a a' -> b && Rel.teq_nosmt_force env (fst a) (fst a'))
            true
            args
            l))
      !unfolded

(** The main check for strict positivity

      Checks if ty_lid (defined mutually with mutuals)
      occurs strictly positively in the type `in_type`
*)
let rec ty_strictly_positive_in_type (env:env)
                                     (mutuals:list lident)
                                     (ty_lid:lident)
                                     (in_type:term)
                                     (unfolded:unfolded_memo_t)
  : bool
  = debug_positivity env (fun _ ->
       "Checking strict positivity in type: " ^ (Print.term_to_string in_type));
    //normalize the type to unfold any type abbreviations
    let in_type = normalize env in_type in
    debug_positivity env (fun _ ->
      "Checking strict positivity in type, after normalization: " ^
            (Print.term_to_string in_type));
    if not (ty_occurs_in ty_lid in_type)
    then true   //ty does not occur in in_type, so obviously strictly positive
    else (
      debug_positivity env (fun _ -> "ty does occur in this type");
      
      match (SS.compress in_type).n with
      | Tm_fvar _
      | Tm_uinst _ 
      | Tm_type _ ->
        debug_positivity env (fun _ ->
          "Checking strict positivity in an fvar/Tm_uinst/Tm_type, return true");
        true  //Type, and fvar constants are fine
      
      | Tm_ascribed (t, _, _)
      | Tm_meta (t, _) ->
        ty_strictly_positive_in_type env mutuals ty_lid t unfolded

      | Tm_app (t, args) ->  //the binder type is an application
        let fv_or_name_opt = term_as_fv_or_name t in
        begin
        match fv_or_name_opt with
        | None ->
          debug_positivity env (fun _ -> 
            BU.format2 "Failed to check positivity of %s in a term with head %s"
                       (Ident.string_of_lid ty_lid)
                       (Print.term_to_string t));
          false
          
        | Some (Inr _) -> //head is a bv
          begin
          debug_positivity env (fun () -> "ty is an app node with head that is a bv");
          //
          // AR: note that we are dropping the guard here
          //     the inductive has already been typechecked, so things are well-typed
          //
          let head_ty, _ =
            env.typeof_well_typed_tot_or_gtot_term
                env
                t
                (let must_tot = false in must_tot)
          in
          check_ty_strictly_positive_in_args env mutuals ty_lid head_ty args unfolded
          end
          
        | Some (Inl (fv, us)) ->
          begin
          if Ident.lid_equals fv.fv_name.v ty_lid
          || FStar.Compiler.List.existsML (Ident.lid_equals fv.fv_name.v) mutuals
          then (
            //if the head is ty_lid or one of its mutually inductive types
            //then check that ty_lid does not occur in the arguments
            //
            //E.g., we forbid `type t a = | T : t (t a) -> t a`
            //            and `type t a = | T : s (t a) -> t a
            //                 and  s a = | S : t a -> s a`
            debug_positivity env (fun _ ->
                BU.format1 
                  "Checking strict positivity in the Tm_app node where head lid is %s itself, \
                   checking that ty does not occur in the arguments"
                  (Ident.string_of_lid ty_lid));
            List.for_all (fun (t, _) -> not (ty_occurs_in ty_lid t)) args
          )
          else (
            //check that the application is either to an inductive
            //that we can show is strictly positive
            //or is an fvar whose arguments are suitably decorated
            //with strictly_positive attributes
            debug_positivity env (fun _ -> 
              BU.format1 "Checking strict positivity in the Tm_app node, \
                          head lid is not %s, so checking nested positivity"
                         (Ident.string_of_lid ty_lid));
            ty_strictly_positive_in_arguments_to_fvar 
              env
              mutuals
              ty_lid
              fv.fv_name.v 
              us
              args
              unfolded
          )
          end
     end

   | Tm_arrow (_, c) ->  //in_type is an arrow
     debug_positivity env (fun () -> "Checking strict positivity in Tm_arrow");
     let check_comp =
       U.is_pure_or_ghost_comp c ||
       (c |> U.comp_effect_name
          |> Env.norm_eff_name env
          |> Env.lookup_effect_quals env
          |> List.contains S.TotalEffect) in
     if not check_comp
     then (
       debug_positivity env (fun _ ->
         "Checking strict positivity , the arrow is impure, so return true");
       true
     )
     else (
       debug_positivity env (fun _ ->
         "Checking strict positivity for an arrow, checking \
          that ty does not occur in the binders, \
          and that it is strictly positive in the return type");
       let sbs, c = U.arrow_formals_comp in_type in
       let return_type = FStar.Syntax.Util.comp_result c in
       let ty_lid_not_to_left_of_arrow =
           List.for_all 
             (fun ({binder_bv=b}) -> not (ty_occurs_in ty_lid b.sort))
             sbs
       in
       if ty_lid_not_to_left_of_arrow
       then (
         (* and is strictly positive also in the return type  *)
         ty_strictly_positive_in_type 
           (push_binders env sbs)
           mutuals
           ty_lid
           return_type
           unfolded
       )
       else false
     )
     
     
   | Tm_refine (bv, f) ->
     debug_positivity env (fun _ ->
       "Checking strict positivity in an Tm_refine, recur in the bv sort)");
     let [b], f = SS.open_term [S.mk_binder bv] f in
     if ty_strictly_positive_in_type env mutuals ty_lid b.binder_bv.sort unfolded
     then let env = push_binders env [b] in
          ty_strictly_positive_in_type env mutuals ty_lid f unfolded
     else false
     
   | Tm_match (scrutinee, _, branches, _) ->
     debug_positivity env (fun _ ->
       "Checking strict positivity in an Tm_match, recur in the branches)");
     if L.existsML (fun mutual -> ty_occurs_in mutual scrutinee) (ty_lid::mutuals)
     then (
       //Do not allow things like
       // type t = | MkT : match f t with ... 
       false
     )
     else (
       List.for_all
         (fun (p, _, t) ->
           let bs = List.map mk_binder (pat_bvs p) in
           let bs, t = SS.open_term bs t in
           ty_strictly_positive_in_type (push_binders env bs) mutuals ty_lid t unfolded)
         branches
     )
            
   | Tm_abs _ -> 
     let bs, body, _ = U.abs_formals in_type in
     let rec aux env bs = 
       match bs with
       | [] -> ty_strictly_positive_in_type env mutuals ty_lid body unfolded
       | b::bs ->
         if ty_strictly_positive_in_type env mutuals ty_lid b.binder_bv.sort unfolded
         then (
           let env = push_binders env [b] in
           aux env bs
         )
         else false
     in
     aux env bs
     
   | _ ->
     debug_positivity env (fun _ ->
       BU.format2
         "Checking strict positivity, unexpected tag: %s and term %s"
           (Print.tag_of_term in_type)
           (Print.term_to_string in_type));
     //Reject remaining cases conservatively as non positive
     false) 

(*
 * We are checking for positive occurrences of ty_lid in a term
 *   (head args), and we know ty_lid occurs somewhere in args
 * In some env, we also have    env |- head : Tot t
 *
 * This function checks that whereever ty_lid appears in the args,
 *   the corresponding parameter in t is marked strictly positive
 *)
and check_ty_strictly_positive_in_args (env:env)
                                       (mutuals:list lident)
                                       (ty_lid:lident)
                                       (head_t:typ)
                                       (args:args)
                                       (unfolded:unfolded_memo_t)
  : bool
  = let bs, _ = U.arrow_formals head_t in
    let rec aux (bs:binders) args
      : bool
      = match bs, args with
        | _, [] ->
          //A partial application: we've checked all the arguments
          true
        
        | [], _ ->
          //More args than binders, e.g., because the remaining arguments
          //Are beneath a computation type
          //In this case, we just insist that ty_lid simply does not occur
          //in the remaining arguments
          List.for_all (fun (arg, _) -> not (ty_occurs_in ty_lid arg)) args
          
        | b::bs, (arg, _)::args ->
          debug_positivity env (fun _ -> 
            BU.format3 "Checking positivity of %s in argument %s and binder %s"
                       (Ident.string_of_lid ty_lid)
                       (Print.term_to_string arg)
                       (Print.binder_to_string b));
                       
          let this_occurrence_ok = 
            // either the ty_lid does not occur at all in the argument
            not (ty_occurs_in ty_lid arg) ||
            // Or the binder is marked strictly positive
            // and the occurrence of ty_lid in arg is also strictly positive
            // E.g., val f ([@@@strictly_positive] a : Type) : Type
            // the binder is ([@@@strictly_positive] a : Type)
            // and
            //       type t = | T of f t     is okay
            // but   type t = | T of f (t -> unit) is not okay
            (U.has_attribute b.binder_attrs FStar.Parser.Const.binder_strictly_positive_attr &&
             ty_strictly_positive_in_type env mutuals ty_lid arg unfolded)
             
          in
          if not this_occurrence_ok
          then ( 
            debug_positivity env (fun _ -> 
              BU.format3 "Failed checking positivity of %s in argument %s and binder %s"
                              (Ident.string_of_lid ty_lid)
                              (Print.term_to_string arg)
                              (Print.binder_to_string b));
            false
          ) else (
            aux bs args
          ) 
  in
  aux bs args


(*  We are checking that `ty_lid` is strictly positive
    in (f args) and ty_lid <> f

    There are two main cases:

      1. f is itself an inductive type, not defined mutually with ty_lid.
         Look at all the constructors of `f` and check that ty_lid
         is strictly positive in the types of all those constructors.
         
         This is to account for the case where `f` has not been decorated
         with strictly_positive attributes on its parameters.

         This may involve unfolding `f` for this application, and since `f`
         is inductive, we need to prevent infinite unfoldings. For this, the
         unfolded:unfolded_memo_t is a memoization table which tracks which
         inductives have already been unfolded, so we don't unfold them again
         when they are re-encountered.

      2. f is not an inductive type (or at least not visibly so, e.g., due
         to an abstraction boundary). In this case, check that for every
         ty_lid is strictly_positive in all the args of f, using
         check_ty_strictly_positive_in_args
     
*)
and ty_strictly_positive_in_arguments_to_fvar
                                    (env:env)
                                    (mutuals:list lident)
                                    (ty_lid:lident)
                                    (fv:lident)
                                    (us:universes)
                                    (args:args)
                                    (unfolded:unfolded_memo_t)
  : bool
  = debug_positivity env (fun _ ->
        BU.format3 "Checking positivity of %s in application of fv %s to %s"
                   (string_of_lid ty_lid)
                   (string_of_lid fv)
                   (Print.args_to_string args));
    let fv_ty = 
      match Env.try_lookup_lid env fv with
      | Some ((_, fv_ty), _) -> fv_ty
      | _ ->
        raise_error 
          (Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
           BU.format1 "Type of %s not found when checking positivity"
                      (string_of_lid fv))
          (range_of_lid fv)
    in
    let b, idatas = datacons_of_typ env fv in
    if not b
    then ( 
      (*
       * Check if ilid's corresponding binder is marked "strictly_positive"
       *)
      check_ty_strictly_positive_in_args env mutuals ty_lid fv_ty args unfolded
    )
    //if fv has already been unfolded with same arguments, return true
    else (
      let ilid = fv in //fv is an inductive
      let no_occurrence_in_indexes (indexes:list arg) =
          L.iter 
            (fun (index, _) ->
              match L.tryFind (fun mutual -> ty_occurs_in mutual index) (ty_lid::mutuals) with
              | Some mutual ->
                raise_error
                  (Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                    BU.format2 "Type %s is not strictly positive since it instantiates \
                               a non-uniformly recursive parameter or index of %s"
                              (string_of_lid mutual)
                              (string_of_lid fv))
                  (range_of_lid fv)
              | _ -> ())
            indexes
      in
      //note that num_ibs gives us only the type parameters,
      //and not indexes, which is what we need since we will
      //substitute them in the data constructor type
      let num_params = Option.get (num_inductive_ty_params env ilid) in
      let params, indexes = List.splitAt num_params args in            
      let fv_formals, _ = U.arrow_formals fv_ty in
      if num_params > List.length fv_formals
      then raise_error (Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                              BU.format4 "Expected a type with %s parameters, \
                                          but %s : %s has only %s parameters"
                                         (string_of_int num_params)
                                         (string_of_lid fv)
                                         (Print.term_to_string fv_ty)
                                         (string_of_int (List.length fv_formals)))
                             (range_of_lid fv);
      let fv_params = fst (List.splitAt num_params fv_formals) in
      let rec prefix_of_uniform_params uniform_params params formals =
          match params, formals with
          | [], [] -> List.rev uniform_params, []
          | p::params, f::formals ->
            if U.has_attribute f.binder_attrs
                               C.binder_non_uniformly_recursive_parameter_attr
            then List.rev uniform_params, p::params
            else prefix_of_uniform_params (p::uniform_params) params formals
          | _ -> failwith "impossible: they have the same length"
      in
      let params, non_uniform_params = prefix_of_uniform_params [] params fv_params in
      let indexes = non_uniform_params@indexes in
      no_occurrence_in_indexes indexes;
      if already_unfolded ilid args unfolded env
      then (
        debug_positivity env (fun _ ->
          "Checking nested positivity, we have already unfolded this inductive with these args");
        true
      )
      else (
        let num_uniform_params = List.length params in
        debug_positivity env (fun _ -> 
          BU.format3 "Checking positivity in datacon, number of type parameters is %s, \
                      adding %s %s to the memo table"          
                     (string_of_int num_uniform_params)
                     (Ident.string_of_lid ilid)
                     (Print.args_to_string params));
        //update the memo table with the inductive name and the args,
        //note we keep only the uniform parameters and not indices
        unfolded := !unfolded @ [ilid, params, num_uniform_params];
        List.for_all
          (fun d -> ty_strictly_positive_in_datacon_of_applied_inductive
                     env
                     mutuals
                     ty_lid
                     d
                     ilid
                     us
                     args
                     num_uniform_params
                     unfolded)
          idatas
      )
    )

(* dlid is a data constructor of ilid
   args are the arguments of the ilid application
   num_ibs is the # of type parameters of ilid
   us are the universes
   
   Check that ty_lid (defined mutually with mutuals)
   occurs strictly positively in every field of dlid *)
and ty_strictly_positive_in_datacon_of_applied_inductive (env:env_t)
                                                         (mutuals:list lident)
                                                         (ty_lid:lident)
                                                         (dlid:lident)
                                                         (ilid:lident)
                                                         (us:universes)
                                                         (args:args)
                                                         (num_ibs:int)
                                                         (unfolded:unfolded_memo_t)
  : bool
  = debug_positivity env (fun _ ->
      BU.format3
        "Checking positivity of %s in data constructor %s : %s"
          (string_of_lid ty_lid)        
          (string_of_lid dlid)
          (string_of_lid ilid));
    let dt =
      match Env.try_lookup_and_inst_lid env us dlid with
      | Some (t, _) -> t
      | None -> 
        raise_error 
          (Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
           BU.format1 "Data constructor %s not found when checking positivity"
                      (string_of_lid dlid))
          (range_of_lid ty_lid)
    in

    debug_positivity env (fun _ ->
      BU.format3
        "Checking positivity in the data constructor type: %s\n\t\
         num_ibs=%s, args=%s,"
         (Print.term_to_string dt)
         (string_of_int num_ibs)
         (Print.args_to_string args));

    //get the number of arguments that cover the type parameters num_ibs,
    //the rest are indexes and these should not mention the mutuals at all
    let args, rest = List.splitAt num_ibs args in
    let check_no_occurrences (rest:list arg) =
      match L.tryFind 
               (fun mutual -> List.existsML (fun (a,_) -> ty_occurs_in mutual a) rest)
               (ty_lid::mutuals)
      with
      | None -> ()
      | Some mutual -> 
        raise_error 
          (Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
           BU.format2 "%s is not strictly positive in %s, since it occurs in an index"
                      (string_of_lid mutual)           
                      (string_of_lid dlid))
          (range_of_lid ty_lid)
    in
    let check_no_index_occurrences (t:term) =
      let head, args = U.head_and_args t in
      match (U.un_uinst head).n with
      | Tm_fvar fv -> 
        begin
        match num_inductive_ty_params env fv.fv_name.v with
        | None -> ()
        | Some n -> check_no_occurrences (snd (List.splitAt n args))
        end
      | _ -> ()
    in
    let applied_dt = apply_datacon_arrow dlid dt args in
    debug_positivity env (fun _ ->
      BU.format3
        "Applied data constructor type: %s %s : %s"
         (string_of_lid dlid)
         (Print.args_to_string args)
         (Print.term_to_string applied_dt));
    let fields, t = U.arrow_formals applied_dt in
    let head, params_indexes = U.head_and_args_full t in    
    check_no_occurrences (snd (List.splitAt num_ibs params_indexes));
    let rec strictly_positive_in_all_fields env fields =
        match fields with
        | [] -> true
        | f::fields ->
          check_no_index_occurrences f.binder_bv.sort;
          if ty_strictly_positive_in_type env mutuals ty_lid f.binder_bv.sort unfolded
          then let env = push_binders env [f] in
               strictly_positive_in_all_fields env fields
          else false
    in
    strictly_positive_in_all_fields env fields

(* Check that the name bv (e.g., a binder annotated with a strictly_positive attribute)
   is strictly positive in t *)
let name_strictly_positive_in_type env (bv:bv) t =
  (* An unqualified long identifier just for positivity-checking
     It cannot clash with any user long identifier, since those
     are always qualified to a module *)
  let fv_lid = set_lid_range (lid_of_str (FStar.Ident.string_of_id bv.ppname)) (range_of_bv bv) in
  let fv = S.tconst fv_lid in
  let t = SS.subst [NT (bv, fv)] t in
  (* For checking if a bv is positive, there are no mutually defined names *)
  ty_strictly_positive_in_type env [] fv_lid t (BU.mk_ref [])


let max_matching_prefix (longer:list 'a) (shorter:list 'b) (f:'a -> 'b -> bool)
  : option int
  = let rec aux n ls ms =
        match ls, ms with
        | _, [] -> Some n
        | l::ls, m::ms -> 
          if f l m then aux (n + 1) ls ms
          else Some n
        | _ -> None
    in
    aux 0 longer shorter
      
let rec min_l (#a:Type) (def:int) (l:list a) (f:a -> int) =
    match l with
    | [] -> def
    | hd::tl -> min (f hd) (min_l def tl f)

let max_recursively_uniform_parameters (env:env_t)
                                       (mutuals:list lident)
                                       (params:list bv)
                                       (ty:term)
  : int
  = let ty = normalize env ty in
    let n_params = L.length params in
    let compare_name_bv (x:arg) (y:bv) =
      match (SS.compress (fst x)).n with
      | Tm_name x -> S.bv_eq x y
      | _ -> false
    in
    let min_l (#a:Type) f l = min_l #a n_params f l in
    let params_to_string () =
        (List.map Print.bv_to_string params |> String.concat ", ")
    in
    debug_positivity env (fun _ ->
      BU.format2 "max_recursively_uniform_parameters? params=%s in %s"
                 (params_to_string())
                 (Print.term_to_string ty));
    let rec aux ty =
        debug_positivity env (fun _ ->
          BU.format1 "max_recursively_uniform_parameters.aux? %s"
                 (Print.term_to_string ty));
        if List.for_all (fun mutual -> not (ty_occurs_in mutual ty)) mutuals
        then n_params
        else (
        match (SS.compress ty).n with
        | Tm_name _
        | Tm_fvar _
        | Tm_uinst _
        | Tm_type _
        | Tm_constant _ ->
          n_params
        | Tm_refine(x, f) ->
          min (aux x.sort)
              (let _, f = SS.open_term [S.mk_binder x] f in
               aux f)
        | Tm_app _ ->
          let head, args = U.head_and_args ty in
          begin
          match (U.un_uinst head).n with
          | Tm_fvar fv ->
            if L.existsML (fv_eq_lid fv) mutuals
            then (
              debug_positivity env (fun _ -> 
                BU.format2 "Searching for max matching prefix of params=%s in args=%s"
                           (params_to_string())
                           (Print.args_to_string args));
              match max_matching_prefix args params compare_name_bv with
              | None -> 0
              | Some n -> n
            )
            else min_l args (fun (arg, _) -> aux arg)
          | _ ->
            min (aux head)
                (min_l args (fun (arg, _) -> aux arg))
          end
        | Tm_abs _ ->
          let bs, body, _ = U.abs_formals ty in
          min (min_l bs (fun b -> aux b.binder_bv.sort))
              (aux body)
        | Tm_arrow _ -> 
          let bs, r = U.arrow_formals ty in
          min (min_l bs (fun b -> aux b.binder_bv.sort))
              (aux r)
        | Tm_match(scrutinee, _, branches, _) ->
          min (aux scrutinee)
              (min_l branches
                     (fun (p, _, t) ->
                       let bs = List.map mk_binder (pat_bvs p) in
                       let bs, t = SS.open_term bs t in
                       aux t))
        | Tm_meta(t, _)
        | Tm_ascribed(t, _, _) ->
          aux t
        | _ ->
          0
        )
    in
    let res = aux ty in
    debug_positivity env (fun _ ->
      BU.format3 "result: max_recursively_uniform_parameters(params=%s in %s) = %s"
                 (params_to_string())
                 (Print.term_to_string ty)
                 (string_of_int res));
    res
    

(*  Check that ty_lid (defined along with mutuals)
    is strictly positive in every field of the data constructor dlid
    AND
    that any parameters of the type annotated with a strictly positive
    attribute is also strictly positive in the fields of the constructor
 *)
let ty_strictly_positive_in_datacon_decl (env:env_t)
                                         (mutuals:list lident)
                                         (ty_lid:lident)
                                         (dlid:lident)
                                         (ty_bs:binders)
                                         (us:universes)
                                         (unfolded:unfolded_memo_t)
  : bool
  = let dt =
      match Env.try_lookup_and_inst_lid env us dlid with
      | Some (t, _) -> t
      | None -> raise_error (Errors.Error_InductiveTypeNotSatisfyPositivityCondition,
                            BU.format1 "Error looking up data constructor %s when checking positivity"
                                       (string_of_lid dlid))
                            (range_of_lid ty_lid)
    in
    debug_positivity env (fun () -> "Checking data constructor type: " ^ (Print.term_to_string dt));
    let raise_unexpected_type () =
        raise_error (Error_InductiveTypeNotSatisfyPositivityCondition,
                     BU.format2 "Unexpected type for data constructor %s : %s"
                                  (Ident.string_of_lid dlid)
                                  (Print.term_to_string dt))
                    (Ident.range_of_lid dlid)
                     
    in
    let check_return_type t =
        let head, args = U.head_and_args t in
        match (U.un_uinst head).n with 
        | Tm_fvar fv ->
          if L.existsML (S.fv_eq_lid fv) mutuals
          then (
            // The constructed type must be one of the mutuals
            // and it should not be of the form t (t ...)
            if 
              L.for_all
                (fun mutual ->
                  L.for_all (fun (arg, _) -> not (ty_occurs_in mutual arg)) args)
                mutuals
            then ()
            else raise_unexpected_type ()
          )
          else (
            raise_unexpected_type ()
          )
        | _ -> 
          raise_unexpected_type ()
    in
    let ty_bs, args = U.args_of_binders ty_bs in
    let dt = apply_datacon_arrow dlid dt args in
    let fields, return_type = U.arrow_formals dt in
    check_return_type return_type;
    let check_annotated_binders_are_strictly_positive_in_field f =
        let incorrectly_annotated_binder =
            L.tryFind 
              (fun b -> 
                 if U.has_attribute b.binder_attrs C.binder_strictly_positive_attr
                 then not (name_strictly_positive_in_type env b.binder_bv f.binder_bv.sort)
                 else false)
              ty_bs
        in
        match incorrectly_annotated_binder with
        | None -> ()
        | Some b ->
          raise_error (Error_InductiveTypeNotSatisfyPositivityCondition,
                       BU.format1 "Binder %s is marked strictly positive, \
                                   but its use in the definition is not"
                                  (Print.binder_to_string b))
                       (range_of_bv b.binder_bv)
    in
    let rec check_all_fields env fields =
        match fields with
        | [] -> true
        | field::fields ->
          check_annotated_binders_are_strictly_positive_in_field field;
          if not (ty_strictly_positive_in_type env mutuals ty_lid field.binder_bv.sort unfolded)
          then false
          else (
            let env = push_binders env [field] in
            check_all_fields env fields
          )
    in
    check_all_fields env fields
      
let open_sig_inductive_typ env se =
    match se.sigel with
    | Sig_inductive_typ (lid, ty_us, ty_params, _, _, _) -> 
      let ty_usubst, ty_us = SS.univ_var_opening ty_us in
      let env = push_univ_vars env ty_us in
      let ty_params = SS.subst_binders ty_usubst ty_params in
      let ty_params = SS.open_binders ty_params in
      let env = push_binders env ty_params in
      env, (lid, ty_us, ty_params)
    | _                                        -> failwith "Impossible!"
  
(* An entry point from the interface:
     Check that the inductive type ty, defined mutually with mutuals
     is strictly positive *)
let check_strict_positivity (env:env_t)
                            (mutuals:list lident)
                            (ty:sigelt)
  : bool
  = //memo table, memoizes the instances of inductives
    //that we have recursively already deemed as strictly positive
    let unfolded_inductives = BU.mk_ref [] in

    //ty_params are the parameters of ty, it does not include the indexes
    let env, (ty_lid, ty_us, ty_params) =  open_sig_inductive_typ env ty in
    let mutuals = ty_lid::mutuals in
    let datacons = snd (datacons_of_typ env ty_lid) in
    List.for_all 
      (fun d ->
         List.for_all
           (fun ty_lid ->
             ty_strictly_positive_in_datacon_decl
               env
               mutuals
               ty_lid
               d
               ty_params
               (List.map U_name ty_us)
               unfolded_inductives)
          mutuals)
    datacons

(* Special-casing the check for exceptions, the single open inductive type we handle. *)
let check_exn_strict_positivity (env:env_t)
                                (data_ctor_lid:lid)
  : bool
  = let unfolded_inductives = BU.mk_ref [] in
    ty_strictly_positive_in_datacon_decl env [C.exn_lid] C.exn_lid data_ctor_lid [] [] unfolded_inductives

let mark_uniform_type_parameters (env:env_t)
                                 (sig:sigelt)
  : sigelt
  = let mark_tycon_parameters tc datas =
        let Sig_inductive_typ (tc_lid, us, ty_param_binders, t, mutuals, data_lids) = tc.sigel in
        let env, (tc_lid, us, ty_params) = open_sig_inductive_typ env tc in
        let _, ty_param_args = U.args_of_binders ty_params in
        let datacon_fields : list (list binder) =
          List.filter_map
            (fun data ->
              match data.sigel with
              | Sig_datacon(d_lid, d_us, dt, tc_lid', _, _) ->
                if Ident.lid_equals tc_lid tc_lid'
                then (
                  let dt = SS.subst (mk_univ_subst d_us (L.map U_name us)) dt in
                  Some (fst (U.arrow_formals (apply_datacon_arrow d_lid dt ty_param_args)))
                )
                else None
              | _ -> None)
            datas
        in
        let ty_param_bvs = L.map (fun b -> b.binder_bv) ty_params in
        let n_params = L.length ty_params in
        let min_l #a f l = min_l #a n_params f l in
        let max_uniform_prefix =
           min_l datacon_fields
                 (fun (fields_of_one_datacon:list binder) ->
                    min_l fields_of_one_datacon 
                          (fun (field:binder) ->
                            max_recursively_uniform_parameters
                              env
                              mutuals
                              ty_param_bvs
                              field.binder_bv.sort))
        in
        let uniformity_flags =
            List.mapi (fun i p -> i < max_uniform_prefix) ty_params
        in
        let attr = 
          let fv = S.lid_as_fv C.binder_non_uniformly_recursive_parameter_attr
                               S.delta_constant
                               None
          in
          S.fv_to_tm fv
        in
        //the suffix of non-uniform parameters is non-uniform
        let _, ty_param_binders_rev =
          List.fold_left2
            (fun (seen_non_uniform, ty_param_binders) 
               this_param_uniform
               ty_param_binder ->
               if seen_non_uniform || not (this_param_uniform)
               then (
                 if U.has_attribute ty_param_binder.binder_attrs C.binder_strictly_positive_attr
                 then ( //if marked strictly positive, it must be uniform
                   raise_error (Error_InductiveTypeNotSatisfyPositivityCondition,
                                BU.format1 "Binder %s is marked strictly positive, \
                                           but it is not uniformly recursive"
                                           (Print.binder_to_string ty_param_binder))
                               (range_of_bv ty_param_binder.binder_bv)
                 );
                 true, { ty_param_binder with binder_attrs=attr::ty_param_binder.binder_attrs}
                       :: ty_param_binders
               )
               else false, ty_param_binder::ty_param_binders)
            (false, [])
            uniformity_flags
            ty_param_binders
        in
        let ty_param_binders = List.rev ty_param_binders_rev in
        let sigel = Sig_inductive_typ (tc_lid, us, ty_param_binders, t, mutuals, data_lids) in
        { tc with sigel }
    in 
    match sig.sigel with
    | Sig_bundle (ses, lids) ->
      let tcs, datas = L.partition (fun se -> Sig_inductive_typ? se.sigel) ses in
      let tcs = List.map (fun tc -> mark_tycon_parameters tc datas) tcs in
      { sig with sigel = Sig_bundle(tcs@datas, lids) }
    
    | _ -> sig
    
