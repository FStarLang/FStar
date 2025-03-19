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

module FStarC.TypeChecker.Positivity

open FStarC
open FStarC
open FStarC.Effect
open FStarC.TypeChecker.Env
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Ident
open FStarC.Errors
open FStar.List.Tot
module S = FStarC.Syntax.Syntax
module SS = FStarC.Syntax.Subst
module BU = FStarC.Util
module U = FStarC.Syntax.Util
module N = FStarC.TypeChecker.Normalize
module L = FStarC.List
module C = FStarC.Parser.Const

open FStarC.Class.Setlike
open FStarC.Class.Show
open FStarC.Class.Tagged

let dbg_Positivity = Debug.get_toggle "Positivity"
let debug_positivity (env:env_t) (msg:unit -> string) : unit =
  if !dbg_Positivity
  then BU.print_string ("Positivity::" ^ msg () ^ "\n")

(**

  This module implements the strict positivity check on inductive type
  definitions

    * The idea of strict positivity is broadly described here:
      http://fstar-lang.org/tutorial/book/part2/part2_inductive_type_families.html#strictly-positive-definitions


    * tests/micro-benchmarks/Positivity.fst provides several 
      small examples to exercises various cases.

  A challenge is that the definition of strict positivity is not
  completely settled among the various dependently typed proof
  assistants. Notably, Lean, Coq, Agda, all implement slight
  variations, all incomparable in permissiveness.

  What is standard is that every occurrence of the type in question
  must be strictly positive, i.e., no occurrences allowed to the left
  of an arrow.

  However, there is a lot of variation in how the indices and
  parameters of an inductive type are handled.

  Here's a summary of what F* supports:

  1. Non-uniformly recursive parameters

     type t a b c = 
       | T : t a (b & b) c -> t a b c


     Here, a is uniformly recursive.
     b is non-uniformly recursive.     
     Since c follows b, which is non-uniform, it is also considered non-uniform
     
     i.e., only a prefix of the parameters may be considered uniform

  2. For an inductive type constructor, every non-uniform parameter or index
     may be considered to be an _arity_ or not

     An arity is a `Type`, or an arrow `t -> arity`

     A term is indexed by an arity if it has type t0 -> ... -> tn -> Type
     and any of the ti are themselves arities

     Given a well-typed term `t v0 ... vn`, we check that if the type of the prefix `t [v0...vi)` 
     is `ti -> ... Type`
     and if `ti` is an arity (and is the type of `vi`)
     then the type being defined cannot appear free in `vi`
     

     E.g., Consider a term  (t :   a:Type -> x:a -> x -> (Type -> Type) -> bool -> Type)
           applied as (t Type nat 0 option true)
           The first index of t is an arity
           (t Type : x:Type -> x -> (Type -> Type) -> bool -> Type) is arity indexed
           (t Type nat : nat -> ...) is not arity indexed
           (t Type nat 0 : (Type -> Type) -> ...) is arity indexed
           (t Type nat 0 option : bool -> Type) is not arity indexed
           (t Type nat 0 option true : Type) is not arity indexed           
           
  3. A type t is strictly-positive in the indexing of s, if `t` does
     not appear free in any of the arity indexes of s.

     E.g., 

     type s (a:Type) : bool -> Type =
       | S : s a true

     type t =
       | T : f:option t -> s t (Some? #t f) -> t

     The type `t` is well-formed in `s t (Some? #t f)`
     since it appears only in a parameter of `s`
     and in a non-arity index of s
     

     However, this is forbidden:

     type f (a:Type -> Type) : Type 
     
     type t : Type -> Type = 
       | T : t (f t)

     since although in `f t`, `t` only instantiates a parameter of `f`
     in `t (f t)`, `t` appears free in an arity index of `t` itself

     Note, Agda does allow the type `t` above, although it rejects

     type t : Type -> Type
       | T : t (t bool)
 *)
 
////////////////////////////////////////////////////////////////////////////////
// Some general utilities
////////////////////////////////////////////////////////////////////////////////

(* A debugging utility to print a list of lids *)
let string_of_lids lids =
    List.map string_of_lid lids |> String.concat ", "

(* Normalize a term before checking for non-strictly positive occurrences *)
let normalize env t =
    N.normalize [Env.Beta;
                 Env.HNF;
                 Env.Weak;
                 Env.Iota;
                 Env.Exclude Env.Zeta;
                 Env.UnfoldUntil delta_constant]
                 env
                 t


(* Given a type or data constructor d : dt
   and parameters to an instance of the type
   instantiate the arguments of d corresponding to the type parameters
   with all_params *)
let apply_constr_arrow (dlid:lident) (dt:term) (all_params:list arg)
  : term 
  = let rec aux t args =
        match (SS.compress t).n, args with
        | _, [] -> U.canon_arrow t
        | Tm_arrow {bs=b::bs; comp=c}, a::args ->
          let tail = 
            match bs with
            | [] -> U.comp_result c
            | _ -> S.mk (Tm_arrow {bs; comp=c}) t.pos
          in
          let b, tail = SS.open_term_1 b tail in
          let tail = SS.subst [NT(b.binder_bv, fst a)] tail in
          aux tail args
        | _ ->
          raise_error 
             (Ident.range_of_lid dlid)
             Errors.Error_InductiveTypeNotSatisfyPositivityCondition
             (BU.format3 "Unexpected application of type parameters %s to a data constructor %s : %s"
                         (Print.args_to_string all_params)
                         (show dlid)
                         (show dt))
    in
    aux dt all_params

(* Checks if ty_lid appears as an fvar in t *)
let ty_occurs_in (ty_lid:lident)
                 (t:term)
  : bool
  = mem ty_lid (Free.fvars t)

(* Checks if `t` is a name or fv and returns it, if so. *)
let rec term_as_fv_or_name (t:term) 
  : option (either (fv & universes) bv)
  = match (SS.compress t).n with
    | Tm_name x -> 
      Some (Inr x)
      
    | Tm_fvar fv ->
      Some (Inl (fv, []))
      
    | Tm_uinst (t, us) ->
      (match (SS.compress t).n with
       | Tm_fvar fv -> Some (Inl (fv, us))
       | _ -> failwith "term_as_fv_or_name: impossible non fvar in uinst")
      
    | Tm_ascribed {tm=t} -> 
      term_as_fv_or_name t
      
    | _ -> None

let open_sig_inductive_typ env se =
    match se.sigel with
    | Sig_inductive_typ {lid; us=ty_us; params=ty_params} -> 
      let ty_usubst, ty_us = SS.univ_var_opening ty_us in
      let env = push_univ_vars env ty_us in
      let ty_params = SS.subst_binders ty_usubst ty_params in
      let ty_params = SS.open_binders ty_params in
      let env = push_binders env ty_params in
      env, (lid, ty_us, ty_params)
    | _                                        -> failwith "Impossible!"

(* Map bv to an unqualified long identifier with the same pp_name
   just for positivity-checking.
     
   It cannot clash with any user long identifier, since those
   are always qualified to a module 
*)
let name_as_fv_in_t (t:term) (bv:bv)
  : term & lident
  = let fv_lid = set_lid_range (lid_of_str (FStarC.Ident.string_of_id bv.ppname)) (range_of_bv bv) in
    let fv = S.tconst fv_lid in
    let t = SS.subst [NT (bv, fv)] t in
    t, fv_lid

////////////////////////////////////////////////////////////////////////////////
// Uniformly recursive parameters
////////////////////////////////////////////////////////////////////////////////

(* The least value of f on the elements of l, or def if l is empty *)
let rec min_l (#a:Type) (def:int) (l:list a) (f:a -> int) =
    match l with
    | [] -> def
    | hd::tl -> min (f hd) (min_l def tl f)

(* For each m in mutuals,
   find the greatest prefix of (p0...pi) of params such that
   every occurrence of m in ty
   is of the form (m p0 ... pi)

   The (p0 ... pi) are uniformly recursive in ty.

   If m does not occur in ty, then ALL the params are considered uniformly recursive
 *)
let max_uniformly_recursive_parameters (env:env_t)
                                       (mutuals:list lident)
                                       (params:list bv)
                                       (ty:term)
  : int
  = let max_matching_prefix (longer:list 'a) (shorter:list 'b) (f:'a -> 'b -> bool)
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
    in
    let ty = normalize env ty in
    let n_params = L.length params in
    let compare_name_bv (x:arg) (y:bv) =
      match (SS.compress (fst x)).n with
      | Tm_name x -> S.bv_eq x y
      | _ -> false
    in
    let min_l (#a:Type) f l = min_l #a n_params f l in
    let params_to_string () =
        (List.map show params |> String.concat ", ")
    in
    debug_positivity env (fun _ ->
      BU.format2 "max_uniformly_recursive_parameters? params=%s in %s"
                 (params_to_string())
                 (show ty));
    let rec aux ty =
        debug_positivity env (fun _ ->
          BU.format1 "max_uniformly_recursive_parameters.aux? %s"
                 (show ty));
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
        | Tm_refine {b=x; phi=f} ->
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
        | Tm_match {scrutinee; brs=branches} ->
          min (aux scrutinee)
              (min_l branches
                     (fun (p, _, t) ->
                       let bs = List.map mk_binder (pat_bvs p) in
                       let bs, t = SS.open_term bs t in
                       aux t))
        | Tm_meta {tm=t}
        | Tm_ascribed {tm=t} ->
          aux t
        | _ ->
          0
        )
    in
    let res = aux ty in
    debug_positivity env (fun _ ->
      BU.format3 "result: max_uniformly_recursive_parameters(params=%s in %s) = %s"
                 (params_to_string())
                 (show ty)
                 (string_of_int res));
    res

(* The sig : sigelt is a Sig_bundle describing a mutually inductive nest of types

   For every type constructor Sig_inductive_typ, find the greatest prefix of
   its parameters that occur uniformly recursively in all its data
   constructors.

   This populates the num_uniform_parameters field of the Sig_inductive_typ

   Note: Every parameter marked strictly_positive MUST be uniformly recursive

*)
let mark_uniform_type_parameters (env:env_t)
                                 (sig:sigelt)
  : sigelt
  = let mark_tycon_parameters tc datas =
        let Sig_inductive_typ {lid=tc_lid; us; params=ty_param_binders; t; mutuals; ds=data_lids; injective_type_params } = tc.sigel in
        let env, (tc_lid, us, ty_params) = open_sig_inductive_typ env tc in
        let _, ty_param_args = U.args_of_binders ty_params in
        let datacon_fields : list (list binder) =
          List.filter_map
            (fun data ->
              match data.sigel with
              | Sig_datacon {lid=d_lid; us=d_us; t=dt; ty_lid=tc_lid'} ->
                if Ident.lid_equals tc_lid tc_lid'
                then (
                  let dt = SS.subst (mk_univ_subst d_us (L.map U_name us)) dt in
                  Some (fst (U.arrow_formals (apply_constr_arrow d_lid dt ty_param_args)))
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
                            max_uniformly_recursive_parameters
                              env
                              mutuals
                              ty_param_bvs
                              field.binder_bv.sort))
        in
        if max_uniform_prefix < n_params
        then (
          let _, non_uniform_params = List.splitAt max_uniform_prefix ty_param_binders in
          List.iter 
            (fun param ->
                 if param.binder_positivity = Some BinderStrictlyPositive
                 then ( //if marked strictly positive, it must be uniform
                   raise_error 
                               (range_of_bv param.binder_bv)
                     Error_InductiveTypeNotSatisfyPositivityCondition
                     (BU.format1 "Binder %s is marked strictly positive, \
                                 but it is not uniformly recursive"
                                 (show param))
                 ))
            non_uniform_params
        );            
        let sigel = Sig_inductive_typ {lid=tc_lid;
                                       us;
                                       params=ty_param_binders;
                                       num_uniform_params=Some max_uniform_prefix;
                                       t;
                                       mutuals;
                                       ds=data_lids;
                                       injective_type_params} in
        { tc with sigel }
    in 
    match sig.sigel with
    | Sig_bundle {ses; lids} ->
      let tcs, datas = L.partition (fun se -> Sig_inductive_typ? se.sigel) ses in
      let tcs = List.map (fun tc -> mark_tycon_parameters tc datas) tcs in
      { sig with sigel = Sig_bundle {ses=tcs@datas; lids} }
    
    | _ -> sig

////////////////////////////////////////////////////////////////////////////////
// Arities and indexes
////////////////////////////////////////////////////////////////////////////////

(* Decides if t could be an arity? i.e., a Type or a t -> ... -> Type? *)
let may_be_an_arity env (t:term)
  : bool
  = let t = normalize env t in
    let rec aux t =
      match (SS.compress t).n with
      | Tm_name _
      | Tm_constant _
      | Tm_abs _
      | Tm_lazy _
      | Tm_quoted _ -> false

      | Tm_fvar _
      | Tm_uinst _
      | Tm_app _ -> (
        let head, args = U.head_and_args t in
        match (U.un_uinst head).n with
        | Tm_fvar fv ->
          (match Env.lookup_sigelt env fv.fv_name.v with
           | None ->
             //We couldn't find it; err conservatively ... this could be an arity
             true
           | Some se ->
             match se.sigel with
             | Sig_let _ ->
               true //maybe an arity, this definition was not unfolded
             | _ -> false
           )
           
        | _ -> true //maybe
        )
        
      | Tm_type _ -> true
      | Tm_arrow _ ->
        let _, t = U.arrow_formals t in
        aux t
      | Tm_refine {b=x} -> aux x.sort
      | Tm_match {brs=branches} ->
        List.existsML
         (fun (p, _, t) ->
           let bs = List.map mk_binder (pat_bvs p) in
           let bs, t = SS.open_term bs t in
           aux t)
         branches

      | Tm_meta {tm=t}
      | Tm_ascribed {tm=t} ->
        aux t

      (* maybes *)
      | Tm_uvar _
      | Tm_let _ ->
        true

      | Tm_delayed _
      | Tm_bvar _
      | Tm_unknown ->
        failwith "Impossible"
    in
    aux t
        
(* t is an application of a type constructor T ps is 
   with parameters ps and indexes is.
   
   Check that the mutuals do not occur in any of the indexes
   whose instantiated type may be arity.

   See the comment at the head of the file for some context about
   indexes and arities
 *)
let check_no_index_occurrences_in_arities env mutuals (t:term) =
  debug_positivity env (fun _ ->
    BU.format2 "check_no_index_occurrences of (mutuals %s) in arities of %s"
      (string_of_lids mutuals)
      (show t));

  (* Check that none of the mutuals appear free in the index term *)
  let no_occurrence_in_index fv mutuals (index:arg) =
    (* The built-in predicates:
         FStar.FunctionalExtensionality.on_domain
         FStar.FunctionalExtensionality.on_domain_g
       are special.
     
       Their two type arguments do not count towards positivity,
       since they are there only as an artifact of describing the
       type of their third argument
   *)
   let fext_on_domain_index_sub_term index =
     let head, args = U.head_and_args index in
     match (U.un_uinst head).n, args with
     | Tm_fvar fv, [_td; _tr; (f, _)] -> 
       if S.fv_eq_lid fv C.fext_on_domain_lid 
       ||  S.fv_eq_lid fv C.fext_on_domain_g_lid
       then f (* if the index is on_domain(_g) #t #s f, 
                 return only f *)
       else index
     | _ -> index
   in
   let index, _ = index in
   L.iter (fun mutual -> 
             if ty_occurs_in mutual (fext_on_domain_index_sub_term index)
             then raise_error index Errors.Error_InductiveTypeNotSatisfyPositivityCondition
                            (BU.format3 "Type %s is not strictly positive since it instantiates \
                                        a non-uniformly recursive parameter or index %s of %s"
                              (string_of_lid mutual)
                              (show index)
                              (string_of_lid fv)))
          mutuals
  in
  let no_occurrence_in_indexes fv mutuals (indexes:list arg) =
      L.iter (no_occurrence_in_index fv mutuals) indexes
  in
  let head, args = U.head_and_args t in
  match (U.un_uinst head).n with
  | Tm_fvar fv -> 
    begin
    match Env.num_inductive_uniform_ty_params env fv.fv_name.v with
    | None -> 
      //the head is not (visibly) a inductive type; nothing to check
      ()
    | Some n ->
      if List.length args <= n
      then () //they are all uniform parameters, nothing to check
      else (
        match Env.try_lookup_lid env fv.fv_name.v with
        | None -> no_occurrence_in_indexes fv.fv_name.v mutuals args
        | Some ((_us, i_typ), _) ->
          debug_positivity env (fun _ -> 
            BU.format2 "Checking arity indexes of %s (num uniform params = %s)"
                     (show t)
                     (string_of_int n));
          let params, indices = List.splitAt n args in
          let inst_i_typ = apply_constr_arrow fv.fv_name.v i_typ params in
          let formals, _sort = U.arrow_formals inst_i_typ in
          let rec aux subst formals indices =
            match formals, indices with
            | _, [] -> ()
            | f::formals, i::indices ->
              let f_t = SS.subst subst f.binder_bv.sort in
              if may_be_an_arity env f_t
              then (
                debug_positivity env (fun _ ->
                  BU.format2 "Checking %s : %s (arity)"
                    (show (fst i))
                    (show f_t));
                no_occurrence_in_index fv.fv_name.v mutuals i
              )
              else (
                debug_positivity env (fun _ ->
                  BU.format2 "Skipping %s : %s (non-arity)"
                    (show (fst i))
                    (show f_t))
              );
              let subst = NT(f.binder_bv, fst i)::subst in
              aux subst formals indices
            | [], _ ->
              no_occurrence_in_indexes fv.fv_name.v mutuals indices
          in
          aux [] formals indices
        )
      end
  | _ -> ()

////////////////////////////////////////////////////////////////////////////////
// Do the mutuals not occur in t?
// Or, if they do, do they only instantiate unused parameters?
// Expects t to be normalized
////////////////////////////////////////////////////////////////////////////////
let mutuals_unused_in_type (mutuals:list lident) t =
  let mutuals_occur_in t = BU.for_some (fun lid -> ty_occurs_in lid t) mutuals in
  let rec ok t =
    if not (mutuals_occur_in t) then true else
    // fv_lid is used in t
    // but we need to check that its occurrences only occur as arguments
    // to functions whose corresponding paramaters are marked as unused
    match (SS.compress t).n with
     | Tm_bvar _
     | Tm_name _
     | Tm_constant _
     | Tm_type _ ->
      //these cases violate the precondition that fv_lid is used in t
      //so we should never get here
       true
     | Tm_fvar _ 
     | Tm_uinst _ ->
      //in these cases, fv_lid is used in t
       false
     | Tm_abs {bs; body=t} ->
       binders_ok bs && ok t
     | Tm_arrow {bs; comp=c} ->
       binders_ok bs && ok_comp c
     | Tm_refine {b=bv; phi=t} ->
       ok bv.sort && ok t
     | Tm_app {hd=head; args} ->
       if mutuals_occur_in head
       then false
       else List.for_all
              (fun (a, qual) -> 
                (match qual with
                 | None -> false
                 | Some q -> U.contains_unused_attribute q.aqual_attributes) ||
                ok a)
              args
      | Tm_match {scrutinee=t; brs=branches} ->
        ok t &&
        List.for_all
            (fun (_, _, br) -> ok br)
             branches
      | Tm_ascribed {tm=t; asc} ->
        ok t
      | Tm_let {lbs=(_, lbs); body=t} ->
        List.for_all (fun lb -> ok lb.lbtyp && ok lb.lbdef) lbs
        && ok t
      | Tm_uvar _ ->
        false
      | Tm_delayed _ ->
        false
      | Tm_meta {tm=t} ->
        ok t
      | _ ->
        false
  and binders_ok bs =
    List.for_all (fun b -> ok b.binder_bv.sort) bs
  and ok_comp c =
    match c.n with
    | Total t -> ok t
    | GTotal t -> ok t
    | Comp c ->
      ok c.result_typ &&
      List.for_all (fun (a, _) -> ok a) c.effect_args              
  in
  ok t

////////////////////////////////////////////////////////////////////////////////
// Main strict positivity check
////////////////////////////////////////////////////////////////////////////////

(**
   unfolded_memo_t: This is a key data structure in the 
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

    A summary of its general structure:
    
    There are four mutually recursive functions

    1. ty_strictly_positive_in_type _ mutuals in_type _

       This is the main function and checks that none of the mutuals
       appear in_type in a non-strictly positive position
       and in arity indexes of in_type

    2. ty_strictly_positive_in_args _ mutuals head_t args _

       Given a head term applied to args, where head is of type
       head_t, this checks that if the mutuals appear in a arg, that
       it does so strictly positively and the corresponding binder
       of head_t is marked strictly positive.

       The head term is not an inductive type constructor

    3. ty_strictly_positive_in_arguments_to_fvar _ mutuals t fv _ args _

       fv may or may not be an inductive, and is not one of the
       mutuals, and this checks that all the mutuals are strictly
       positive in the arguments

       if is is not an inductive, we fall back to 2
       if it is an inductive, we check each of its constructors using 4

    4. ty_strictly_positive_in_datacon_of_applied_inductive _ mutuals dlid ilid _ args _ _

       This considers every field of dlid applied to the type
       parameters of the inductive ilid in args, and checks that the
       mutuals are strictly positive in all the field types. 
*)
let rec ty_strictly_positive_in_type (env:env)
                                     (mutuals:list lident)
                                     (in_type:term)
                                     (unfolded:unfolded_memo_t)
  : bool
  = //normalize the type to unfold any type abbreviations
    let in_type = normalize env in_type in
    debug_positivity env (fun _ ->
      BU.format2
        "Checking strict positivity of {%s} in type, after normalization %s "
          (string_of_lids mutuals)
          (show in_type));
    if List.for_all (fun mutual -> not (ty_occurs_in mutual in_type)) mutuals
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
      
      | Tm_ascribed {tm=t}
      | Tm_meta {tm=t} ->
        ty_strictly_positive_in_type env mutuals t unfolded

      | Tm_app {hd=t; args} ->  //the binder type is an application
        let fv_or_name_opt = term_as_fv_or_name t in
        begin
        match fv_or_name_opt with
        | None ->
          debug_positivity env (fun _ -> 
            BU.format2 "Failed to check positivity of %s in a term with head %s"
                       (string_of_lids mutuals)
                       (show t));
          //The head is not a name or an fv
          //conservatively return false
          false
          
        | Some (Inr x) -> //head is an name
          begin
          let head_ty, _pos = Env.lookup_bv env x in
          debug_positivity env (fun _ ->
            BU.format3 "Tm_app, head bv, in_type=%s, head_bv=%s, head_ty=%s"
                       (show in_type)
                       (show x)
                       (show head_ty));
                           
          //The check depends on the strict positivity annotations on the type of the name
          ty_strictly_positive_in_args env mutuals head_ty args unfolded
          end
          
        | Some (Inl (fv, us)) ->
          begin
          if FStarC.List.existsML (Ident.lid_equals fv.fv_name.v) mutuals
          then (
            //if the head is one of the mutually inductive types
            //then check that ty_lid does not occur in the arguments
            //
            //E.g., we forbid `type t a = | T : t (t a) -> t a`
            //            and `type t a = | T : s (t a) -> t a
            //                 and  s a = | S : t a -> s a`
            debug_positivity env (fun _ ->
                BU.format1 
                  "Checking strict positivity in the Tm_app node where head lid is %s itself, \
                   checking that ty does not occur in the arguments"
                  (Ident.string_of_lid fv.fv_name.v));
              List.for_all (fun (t, _) -> mutuals_unused_in_type mutuals t) args
          )
          else (
            //check that the application is either to an inductive
            //that we can show is strictly positive
            //or is an fvar whose arguments are suitably decorated
            //with strictly_positive attributes
            debug_positivity env (fun _ -> 
              BU.format1 "Checking strict positivity in the Tm_app node, \
                          head lid is not in %s, so checking nested positivity"
                          (string_of_lids mutuals));
            ty_strictly_positive_in_arguments_to_fvar 
              env
              mutuals
              in_type
              fv.fv_name.v 
              us
              args
              unfolded
          )
          end
     end

   | Tm_arrow {comp=c} ->  //in_type is an arrow
     debug_positivity env (fun () -> "Checking strict positivity in Tm_arrow");
     let check_comp =
       U.is_pure_or_ghost_comp c ||
       (c |> U.comp_effect_name
          |> Env.norm_eff_name env
          |> Env.lookup_effect_quals env
          |> List.contains S.TotalEffect) in
     if not check_comp
     then (
       //t -> Dv _
       //is accepted as strictly positive in t
       //since it is behind a Dv effect
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
       let return_type = FStarC.Syntax.Util.comp_result c in
       let ty_lid_not_to_left_of_arrow =
            List.for_all 
               (fun ({binder_bv=b}) -> mutuals_unused_in_type mutuals b.sort)
               sbs
       in
       if ty_lid_not_to_left_of_arrow
       then (
         (* and is strictly positive also in the return type  *)
         ty_strictly_positive_in_type 
           (push_binders env sbs)
           mutuals
           return_type
           unfolded
       )
       else false
     )
     
     
   | Tm_refine {b=bv; phi=f} ->
     debug_positivity env (fun _ ->
       "Checking strict positivity in an Tm_refine, recur in the bv sort)");
     let [b], f = SS.open_term [S.mk_binder bv] f in
     if ty_strictly_positive_in_type env mutuals b.binder_bv.sort unfolded
     then let env = push_binders env [b] in
          ty_strictly_positive_in_type env mutuals f unfolded
     else false
     
   | Tm_match {scrutinee; brs=branches} ->
     debug_positivity env (fun _ ->
       "Checking strict positivity in an Tm_match, recur in the branches)");
     if L.existsML (fun mutual -> ty_occurs_in mutual scrutinee) mutuals
     then (
       // type t = | MkT : match f t with | D x -> e
       // is ok if {t,x} are strictly positive in e
       List.for_all
         (fun (p, _, t) ->
           let bs = List.map mk_binder (pat_bvs p) in
           let bs, t = SS.open_term bs t in
           let t, mutuals = 
             List.fold_left
               (fun (t, lids) b -> 
                 let t, lid = name_as_fv_in_t t b.binder_bv in
                 t, lid::lids)
               (t, mutuals)
               bs
           in
           ty_strictly_positive_in_type env mutuals t unfolded)
         branches
     )
     else (
       List.for_all
         (fun (p, _, t) ->
           let bs = List.map mk_binder (pat_bvs p) in
           let bs, t = SS.open_term bs t in
           ty_strictly_positive_in_type (push_binders env bs) mutuals t unfolded)
         branches
     )
            
   | Tm_abs _ -> 
     let bs, body, _ = U.abs_formals in_type in
     //strictly positive in all the binders and the result
     let rec aux env bs = 
       match bs with
       | [] -> ty_strictly_positive_in_type env mutuals body unfolded
       | b::bs ->
         if ty_strictly_positive_in_type env mutuals b.binder_bv.sort unfolded
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
           (tag_of in_type)
           (show in_type));
     //Reject remaining cases conservatively as non positive
     false) 

(*
 * We are checking for positive occurrences of mutuals in a term
 *   (head args), and we know one of the mutuals occurs somewhere in args
 * We also have   env |- head : Tot t
 *
 * This function checks that whereever ty_lid appears in the args,
 *   the corresponding parameter in t is marked strictly positive
 *)
and ty_strictly_positive_in_args (env:env)
                                 (mutuals:list lident)
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
          List.for_all (fun (arg, _) -> mutuals_unused_in_type mutuals arg) args
          
        | b::bs, (arg, _)::args ->
          debug_positivity env (fun _ -> 
            BU.format3 "Checking positivity of %s in argument %s and binder %s"
                       (string_of_lids mutuals)
                       (show arg)
                       (show b));
                       
          let this_occurrence_ok = 
            // either the ty_lid does not occur at all in the argument
            mutuals_unused_in_type mutuals arg ||
            // Or the binder is marked unused
            // E.g., val f ([@@@unused] a : Type) : Type
            // the binder is ([@@@unused] a : Type)
            U.is_binder_unused b ||
            // Or the binder is marked strictly positive
            // and the occurrence of ty_lid in arg is also strictly positive
            // E.g., val f ([@@@strictly_positive] a : Type) : Type
            // the binder is ([@@@strictly_positive] a : Type)
            // and
            //       type t = | T of f t     is okay
            // but   type t = | T of f (t -> unit) is not okay
            (U.is_binder_strictly_positive b &&
             ty_strictly_positive_in_type env mutuals arg unfolded)
             
          in
          if not this_occurrence_ok
          then ( 
            debug_positivity env (fun _ -> 
              BU.format3 "Failed checking positivity of %s in argument %s and binder %s"
                              (string_of_lids mutuals)
                              (show arg)
                              (show b));
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
         to an abstraction boundary). In this case, check that every
         ty_lid is strictly_positive in all the args of f, using
         check_ty_strictly_positive_in_args
     
*)
and ty_strictly_positive_in_arguments_to_fvar
                                    (env:env)
                                    (mutuals:list lident)
                                    (t:term) //t== fv us args
                                    (fv:lident)
                                    (us:universes)
                                    (args:args)
                                    (unfolded:unfolded_memo_t)
  : bool
  = debug_positivity env (fun _ ->
        BU.format4 "Checking positivity of %s in application of fv %s to %s (t=%s)"
                   (string_of_lids mutuals)
                   (string_of_lid fv)
                   (Print.args_to_string args)
                   (show t));
    if Env.is_datacon env fv
    then (
      // If fv is a constructor, then the mutuals must be strictly positive
      // in all the arguments
      List.for_all
        (fun (a, _) -> ty_strictly_positive_in_type env mutuals a unfolded)
        args
    )
    else (
      let fv_ty = 
        match Env.try_lookup_lid env fv with
        | Some ((_, fv_ty), _) -> fv_ty
        | _ ->
          raise_error fv Errors.Error_InductiveTypeNotSatisfyPositivityCondition
            (BU.format1 "Type of %s not found when checking positivity"
                       (string_of_lid fv))
      in
      let b, idatas = datacons_of_typ env fv in
      if not b
      then ( 
        (*
         * Check if ilid's corresponding binder is marked "strictly_positive"
         *)
        ty_strictly_positive_in_args env mutuals fv_ty args unfolded
      )
      //if fv has already been unfolded with same arguments, return true
      else (
        check_no_index_occurrences_in_arities env mutuals t;
        let ilid = fv in //fv is an inductive
        //note that num_ibs gives us only the type parameters,
        //and not indexes, which is what we need since we will
        //substitute them in the data constructor type
        let num_uniform_params = 
          match Env.num_inductive_uniform_ty_params env ilid with
          | None -> //impossible; we know that ilid is an inductive
            failwith "Unexpected type"
          | Some n -> n
        in
        let params, _rest = List.splitAt num_uniform_params args in            
        if already_unfolded ilid args unfolded env
        then (
          debug_positivity env (fun _ ->
            "Checking nested positivity, we have already unfolded this inductive with these args");
          true
        )
        else (
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
                      d
                      ilid
                      us
                      args
                      num_uniform_params
                      unfolded)
            idatas
      )
    )
  )

(* dlid is a data constructor of ilid
   args are the arguments of the ilid application
   num_ibs is the # of type parameters of ilid
   us are the universes
   
   Check that the mutuals
   occur strictly positively in every field of dlid *)
and ty_strictly_positive_in_datacon_of_applied_inductive (env:env_t)
                                                         (mutuals:list lident)
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
          (string_of_lids mutuals)
          (string_of_lid dlid)
          (string_of_lid ilid));
    let dt =
      match Env.try_lookup_and_inst_lid env us dlid with
      | Some (t, _) -> t
      | None -> 
        raise_error 
          (range_of_lid dlid)
          Errors.Error_InductiveTypeNotSatisfyPositivityCondition
          (BU.format1 "Data constructor %s not found when checking positivity"
                      (string_of_lid dlid))
    in

    debug_positivity env (fun _ ->
      BU.format3
        "Checking positivity in the data constructor type: %s\n\t\
         num_ibs=%s, args=%s,"
         (show dt)
         (string_of_int num_ibs)
         (Print.args_to_string args));

    //get the number of arguments that cover the type parameters num_ibs,
    //the rest are indexes and these should not mention the mutuals at all
    let args, rest = List.splitAt num_ibs args in
    let applied_dt = apply_constr_arrow dlid dt args in
    debug_positivity env (fun _ ->
      BU.format3
        "Applied data constructor type: %s %s : %s"
         (string_of_lid dlid)
         (Print.args_to_string args)
         (show applied_dt));
    let fields, t = U.arrow_formals applied_dt in
    check_no_index_occurrences_in_arities env mutuals t;
    let rec strictly_positive_in_all_fields env fields =
        match fields with
        | [] -> true
        | f::fields ->
          debug_positivity env (fun _ ->
            BU.format2 "Checking field %s : %s for indexes and positivity"
              (show f.binder_bv)
              (show f.binder_bv.sort));
          check_no_index_occurrences_in_arities env mutuals f.binder_bv.sort;
          if ty_strictly_positive_in_type env mutuals f.binder_bv.sort unfolded
          then let env = push_binders env [f] in
               strictly_positive_in_all_fields env fields
          else false
    in
    strictly_positive_in_all_fields env fields

////////////////////////////////////////////////////////////////////////////////
// External API for strict positivity checking
////////////////////////////////////////////////////////////////////////////////


(* 
   Check that the name bv (a binder annotated with a strictly_positive
   attribute) is strictly positive in t
*)
let name_strictly_positive_in_type env (bv:bv) t =
  let t, fv_lid = name_as_fv_in_t t bv in
  ty_strictly_positive_in_type env [fv_lid] t (mk_ref [])

  
(* 
   Check that the name bv (a binder annotated with a strictly_positive
   attribute) is strictly positive in t
*)
let name_unused_in_type env (bv:bv) t =
  let t, fv_lid = name_as_fv_in_t t bv in
  not (ty_occurs_in fv_lid t) ||
  mutuals_unused_in_type [fv_lid] (normalize env t)

(*  Check that the mutuals are
    strictly positive in every field of the data constructor dlid
    AND
    that any parameters of the type annotated with a strictly positive
    attribute are also strictly positive in the fields of the constructor

    The env must already contain all the ty_bs
 *)
let ty_strictly_positive_in_datacon_decl (env:env_t)
                                         (mutuals:list lident)
                                         (dlid:lident)
                                         (ty_bs:binders)
                                         (us:universes)
                                         (unfolded:unfolded_memo_t)
  : bool
  = let dt =
      match Env.try_lookup_and_inst_lid env us dlid with
      | Some (t, _) -> t
      | None -> raise_error dlid
                            Errors.Error_InductiveTypeNotSatisfyPositivityCondition
                            (BU.format1 "Error looking up data constructor %s when checking positivity"
                                       (string_of_lid dlid))
    in
    debug_positivity env (fun () -> "Checking data constructor type: " ^ (show dt));
    let ty_bs, args = U.args_of_binders ty_bs in
    let dt = apply_constr_arrow dlid dt args in
    let fields, return_type = U.arrow_formals dt in
    check_no_index_occurrences_in_arities env mutuals return_type;
    let check_annotated_binders_are_strictly_positive_in_field f =
        let incorrectly_annotated_binder =
            L.tryFind 
              (fun b ->
                 (U.is_binder_unused b
                  && not (name_unused_in_type env b.binder_bv f.binder_bv.sort)) ||
                 (U.is_binder_strictly_positive b
                  && not (name_strictly_positive_in_type env b.binder_bv f.binder_bv.sort)))
              ty_bs
        in
        match incorrectly_annotated_binder with
        | None -> ()
        | Some b ->
          raise_error b Error_InductiveTypeNotSatisfyPositivityCondition
                      (BU.format2 "Binder %s is marked %s, \
                                   but its use in the definition is not"
                                  (show b)
                                  (if U.is_binder_strictly_positive b
                                   then "strictly_positive"
                                   else "unused"))
    in
    let rec check_all_fields env fields =
        match fields with
        | [] -> true
        | field::fields ->
          check_annotated_binders_are_strictly_positive_in_field field;
          if not (ty_strictly_positive_in_type env mutuals field.binder_bv.sort unfolded)
          then false
          else (
            let env = push_binders env [field] in
            check_all_fields env fields
          )
    in
    check_all_fields env fields
      
  
(* An entry point from the interface:
     Check that the inductive type ty, defined mutually with mutuals
     is strictly positive *)
let check_strict_positivity (env:env_t)
                            (mutuals:list lident)
                            (ty:sigelt)
  : bool
  = //memo table, memoizes the instances of inductives
    //that we have recursively already deemed as strictly positive
    let unfolded_inductives = mk_ref [] in

    //ty_params are the parameters of ty, it does not include the indexes
    let env, (ty_lid, ty_us, ty_params) = open_sig_inductive_typ env ty in
    let mutuals = List.filter (fun m -> not (Env.is_datacon env m)) mutuals in
    let mutuals = 
      //make sure that ty_lid itself is part of the mutuals
      if List.existsML (Ident.lid_equals ty_lid) mutuals
      then mutuals
      else ty_lid::mutuals in
    let datacons = snd (datacons_of_typ env ty_lid) in
    let us = List.map U_name ty_us in
    List.for_all 
      (fun d ->
           ty_strictly_positive_in_datacon_decl
               env
               mutuals
               d
               ty_params
               us
               unfolded_inductives)
    datacons

(* Special-casing the check for exceptions, the single open inductive type we handle. *)
let check_exn_strict_positivity (env:env_t)
                                (data_ctor_lid:lid)
  : bool
  = let unfolded_inductives = mk_ref [] in
    ty_strictly_positive_in_datacon_decl env [C.exn_lid] data_ctor_lid [] [] unfolded_inductives

    
