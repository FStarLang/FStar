module FStar.InteractiveHelpers.Effectful

module HS = FStar.HyperStack

open FStar.List.Tot
open FStar.Tactics
open FStar.Mul
open FStar.InteractiveHelpers.Base
open FStar.InteractiveHelpers.ExploreTerm
open FStar.InteractiveHelpers.Propositions

let term_eq = FStar.Reflection.TermEq.Simple.term_eq

/// Effectful term analysis: retrieve information about an effectful term, including
/// its return type, its arguments, its correctly instantiated pre/postcondition, etc.

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"


(*** Effectful term analysis *)
/// Cast information
noeq type cast_info = {
  term : term;
  p_ty : option type_info; // The type of the term
  exp_ty : option type_info; // The type of the expected parameter
}

let mk_cast_info t p_ty exp_ty : cast_info =
  Mkcast_info t p_ty exp_ty

val cast_info_to_string : cast_info -> Tac string
let cast_info_to_string info =
  "Mkcast_info (" ^ term_to_string info.term ^ ") (" ^
  option_to_string type_info_to_string info.p_ty ^ ") (" ^
  option_to_string type_info_to_string info.exp_ty ^ ")"

/// Extracts the effectful information from a computation
noeq type effect_info = {
  ei_type : effect_type;
  ei_ret_type : type_info;
  ei_pre : option term;
  ei_post : option term;
}

let mk_effect_info = Mkeffect_info

/// Convert a ``typ_or_comp`` to cast information
val effect_info_to_string : effect_info -> Tac string
let effect_info_to_string c =
  "Mkeffect_info " ^
  effect_type_to_string c.ei_type ^ " (" ^
  option_to_string term_to_string c.ei_pre ^ ") (" ^
  type_info_to_string c.ei_ret_type ^ ") (" ^
  option_to_string term_to_string c.ei_post ^ ")"

/// Effectful term information
noeq type eterm_info = {
  einfo : effect_info;
  (* Head and parameters of the decomposition of the term into a function application *)
  head : term;
  parameters : list cast_info;
}

val eterm_info_to_string : eterm_info -> Tac string
let eterm_info_to_string info =
  let params = map (fun x -> "(" ^ cast_info_to_string x ^ ");  \n") info.parameters in
  let params_str = List.Tot.fold_left (fun x y -> x ^ y) "" params in
  "Mketerm_info (" ^
  effect_info_to_string info.einfo ^ ") (" ^
  term_to_string info.head ^ ")\n[" ^
  params_str ^ "]"

let mk_eterm_info = Mketerm_info


(**** Step 1 *)
/// Decompose a function application between its body and parameters
val decompose_application : env -> term -> Tac (term & list cast_info)

#push-options "--ifuel 1"
let rec decompose_application_aux (e : env) (t : term) :
  Tac (term & list cast_info) =
  match inspect t with
  | Tv_App hd (a, qualif) ->
    let hd0, params = decompose_application_aux e hd in
    (* Parameter type *)
    let a_type = get_type_info e a in
    (* Type expected by the function *)
    let hd_ty = safe_tc e hd in
    let param_type =
      match hd_ty with
      | None -> None
      | Some hd_ty' ->
        match inspect hd_ty' with
        | Tv_Arrow b c ->
          Some (get_type_info_from_type (binder_sort b))
        | _ -> None
    in
    let cast_info = mk_cast_info a a_type param_type in
    hd0, cast_info :: params
  | _ -> t, []
#pop-options

let decompose_application e t =
  let hd, params = decompose_application_aux e t in
  hd, List.Tot.rev params

/// Computes an effect type, its return type and its (optional) pre and post
val comp_view_to_effect_info : dbg:bool -> comp_view -> Tac (option effect_info)

let comp_view_to_effect_info dbg cv =
  match cv with
  | C_Total ret_ty ->
    let ret_type_info = get_type_info_from_type ret_ty in
    Some (mk_effect_info E_Total ret_type_info None None)
  | C_GTotal ret_ty ->
    let ret_type_info = get_type_info_from_type ret_ty in
    Some (mk_effect_info E_Total ret_type_info None None)
  | C_Lemma pre post patterns ->
    (* We use unit as the return type information *)
    let pre = prettify_term dbg pre in
    let post = prettify_term dbg post in
    Some (mk_effect_info E_Lemma unit_type_info (Some pre) (Some post))
  | C_Eff univs eff_name ret_ty eff_args _ ->
    print_dbg dbg ("comp_view_to_effect_info: C_Eff " ^ flatten_name eff_name);
    let ret_type_info = get_type_info_from_type ret_ty in
    let etype = effect_name_to_type eff_name in
    let mk_res = mk_effect_info etype ret_type_info in
    let eff_args = map (fun (x,a) -> (prettify_term dbg x, a)) eff_args in
    begin match etype, eff_args with
    | E_PURE, [(pre, _)] -> Some (mk_res (Some pre) None)
    | E_Pure, [(pre, _); (post, _)]
    | E_Stack, [(pre, _); (post, _)]
    | E_ST, [(pre, _); (post, _)] -> Some (mk_res (Some pre) (Some post))
    (* If the effect is unknown and there are two parameters or less, we make the
     * guess that the first one is a pre-condition and the second one is a
     * post-condition *)
    | E_Unknown, [] -> Some (mk_res None None)
    | E_Unknown, [(pre, _)] -> Some (mk_res (Some pre) None)
    | E_Unknown, [(pre, _); (post, _)] -> Some (mk_res (Some pre) (Some post))
    | _ -> None
    end

val comp_to_effect_info : dbg:bool -> comp -> Tac (option effect_info)

let comp_to_effect_info dbg c =
  let cv : comp_view = inspect_comp c in
  comp_view_to_effect_info dbg cv

val compute_effect_info : dbg:bool -> env -> term -> Tac (option effect_info)

let compute_effect_info dbg e tm =
  match safe_tcc e tm with
  | Some c -> comp_to_effect_info dbg c
  | None -> None

/// Converts a ``typ_or_comp`` to an ``effect_info`` by flushing the instantiations
/// stored in the ``typ_or_comp``.
let typ_or_comp_to_effect_info (dbg : bool) (ge : genv) (c : typ_or_comp) :
  Tac effect_info =
(*  match c with
  | TC_Typ ty pl num_unflushed ->
    let tinfo = get_type_info_from_type ty in
    mk_effect_info E_Total tinfo None None
  | TC_Comp cv pl num_unflushed ->
    let opt_einfo = comp_to_effect_info dbg cv in
    match opt_einfo with
    | None -> mfail ("typ_or_comp_to_effect_info failed on: " ^ acomp_to_string cv)
    | Some einfo -> einfo *)
  let c = flush_typ_or_comp dbg ge.env c in
  match c with
  | TC_Typ ty _ _ ->
    let tinfo = get_type_info_from_type ty in
    mk_effect_info E_Total tinfo None None
  | TC_Comp cv _ _ ->
    let opt_einfo = comp_to_effect_info dbg cv in
    match opt_einfo with
    | None -> mfail ("typ_or_comp_to_effect_info failed on: " ^ acomp_to_string cv)
    | Some einfo -> einfo


/// ``tcc`` often returns a lifted effect which is not what we want (ex.: a
/// lemma called inside a Stack function may have been lifted to Stack, but
/// when studying this term effect, we want to retrieve its non-lifted effect).
/// The workaround is to decompose the term if it is an application, then retrieve
/// the effect of the head, and reconstruct it.
/// Note: I tried inspecting then repacking the term before calling ``tcc`` to
/// see if it allows to "forget" the context: it doesn't work.
val tcc_no_lift : env -> term -> Tac comp

let tcc_no_lift e t =
  match inspect t with
  | Tv_App _ _ ->
    let hd, args = collect_app t in
    let c = tcc e hd in
    inst_comp e c (List.Tot.map fst args)
  | _ ->
    (* Fall back to ``tcc`` *)
    tcc e t

/// Returns the effectful information about a term
val compute_eterm_info : dbg:bool -> env -> term -> Tac eterm_info

#push-options "--ifuel 2"
let compute_eterm_info (dbg : bool) (e : env) (t : term) =
  (* Decompose the term if it is a function application *)
  let hd, parameters = decompose_application e t in
  try
    begin
    let c : comp = tcc_no_lift e t in
    let opt_einfo = comp_to_effect_info dbg c in
    match opt_einfo with
    | None -> mfail ("compute_eterm_info: failed on: " ^ term_to_string t)
    | Some einfo ->
      mk_eterm_info einfo hd parameters
    end
  with
  | TacticFailure (msg, _) ->
    mfail_doc ([text "compute_eterm_info: failure"] @ msg)
  | e -> raise e
#pop-options

(***** Types, casts and refinements *)

(* TODO: those are not needed anymore *)
let has_refinement (ty:type_info) : Tot bool =
  Some? ty.refin

let get_refinement (ty:type_info{Some? ty.refin}) : Tot term =
  Some?.v ty.refin

let get_opt_refinment (ty:type_info) : Tot (option term) =
  ty.refin

let get_rawest_type (ty:type_info) : Tot typ =
  ty.ty

/// Compare the type of a parameter and its expected type
type type_comparison = | Refines | Same_raw_type | Unknown

#push-options "--ifuel 1"
let type_comparison_to_string c =
  match c with
  | Refines -> "Refines"
  | Same_raw_type -> "Same_raw_type"
  | Unknown -> "Unknown"
#pop-options

// TODO: without debugging information generation, is Tot
let compare_types (dbg : bool) (info1 info2 : type_info) :
  Tac (c:type_comparison{c = Same_raw_type ==> has_refinement info2}) =
  print_dbg dbg "[> compare_types";
  if term_eq info1.ty info2.ty then
      let _ = print_dbg dbg "-> types are equal" in
      if has_refinement info2 then
        let _ = print_dbg dbg "-> 2nd type has refinement" in
        // This doesn't work like in C: we need to check if info1 has a
        // refinement, then we can compare the refinements inside ANOTHER if
        if has_refinement info1 then
          let _ = print_dbg dbg "-> 1st type has refinement" in
          if term_eq (get_refinement info1) (get_refinement info2) then
            let _ = print_dbg dbg "-> Refines" in
            Refines
          else
          let _ = print_dbg dbg "-> Same_raw_type" in
          Same_raw_type // Same raw type but can't say anything about the expected refinement
        else
          let _ = print_dbg dbg "-> 1st type has no refinement" in
          let _ = print_dbg dbg "-> Same_raw_type" in
          Same_raw_type // Same raw type but can't say anything about the expected refinement
      else
        let _ = print_dbg dbg "-> 2nd type has no refinement: Refines" in
        Refines // The first type is more precise than the second type
    else
      let _ = print_dbg dbg "types are not equal" in
      Unknown

let compare_cast_types (dbg : bool) (p:cast_info) :
  Tac (c:type_comparison{
    ((c = Refines \/ c = Same_raw_type) ==> (Some? p.p_ty /\ Some? p.exp_ty)) /\
    (c = Same_raw_type ==> has_refinement (Some?.v p.exp_ty))}) =
  print_dbg dbg "[> compare_cast_types";
  match p.p_ty, p.exp_ty with
  | Some info1, Some info2 ->
    compare_types dbg info1 info2
  | _ -> Unknown

(*/// Retrieve the list of types from the parameters stored in ``typ_or_comp``.
val typ_or_comp_to_param_types : typ_or_comp -> Tot (list typ)

let typ_or_comp_to_param_types c =
  let pl = params_of_typ_or_comp c in
  List.Tot.map type_of_binder pl *)

(**** Step 2 *)
/// The retrieved type refinements and post-conditions are not instantiated (they
/// are lambda functions): instantiate them to get propositions.


/// Generate a term of the form [has_type x ty]
val mk_has_type : term -> typ -> Tac term
let mk_has_type t ty =
  let params = [(ty, Q_Implicit); (t, Q_Explicit); (ty, Q_Explicit)] in
  mk_app (`has_type) params  


// TODO: I don't understand why I need ifuel 2 here
#push-options "--ifuel 2"
/// Generate the propositions equivalent to a correct type cast.
/// Note that the type refinements need to be instantiated.
val cast_info_to_propositions : bool -> genv -> cast_info -> Tac (list proposition)
let cast_info_to_propositions dbg ge ci =
  print_dbg dbg ("[> cast_info_to_propositions:\n" ^ cast_info_to_string ci);
  match compare_cast_types dbg ci with
  | Refines -> 
    print_dbg dbg ("-> Comparison result: Refines");
    []
  | Same_raw_type ->
    print_dbg dbg ("-> Comparison result: Same_raw_type");
    let refin = get_refinement (Some?.v ci.exp_ty) in
    let inst_refin = mk_app_norm ge.env refin [ci.term] in
    [inst_refin]
  | Unknown ->
    print_dbg dbg ("-> Comparison result: Unknown");
    match ci.p_ty, ci.exp_ty with
    | Some p_ty, Some e_ty ->
      let p_rty = get_rawest_type p_ty in
      let e_rty = get_rawest_type e_ty in
      (* For the type cast, we generate an assertion of the form:
       * [> has_type (p <: type_of_p) expected_type
       * The reason is that we want the user to know which parameter is
       * concerned (hence the ``has_type``), and which types should be
       * related (hence the ascription).
       *)
      let ascr_term = pack (Tv_AscribedT ci.term p_rty None false) in
      let has_type_params = [(p_rty, Q_Implicit); (ascr_term, Q_Explicit); (e_rty, Q_Explicit)] in
      let type_cast = mk_app (`has_type) has_type_params in
      (* Expected type's refinement *)
      let inst_opt_refin = opt_mk_app_norm ge.env e_ty.refin [ci.term] in
      opt_cons inst_opt_refin [type_cast]
    | _ -> []
#pop-options

/// Generates a list of propositions from a list of ``cast_info``. Note that
/// the user should revert the list before printing the propositions.
val cast_info_list_to_propositions : bool -> genv -> list cast_info -> Tac (list proposition)
let cast_info_list_to_propositions dbg ge ls =
  let lsl = map (cast_info_to_propositions dbg ge) ls in
  flatten lsl

/// When dealing with unknown effects, we try to guess what the pre and post-conditions
/// are. The effects are indeed very likely to have a pre and a post-condition,
/// and to be parameterized with an internal effect state, so that the pre and posts
/// have the following shapes:
/// - pre  : STATE -> Type0
/// - post : STATE -> RET -> STATE -> Type0
/// Or (no state/pure):
/// - pre  : Type0
/// - post : RET -> Type0
/// We try to detect that with the following functions:
noeq type pre_post_type =
| PP_Unknown | PP_Pure
| PP_State : (state_type:term) -> pre_post_type

val compute_pre_type : bool -> env -> term -> Tac pre_post_type
let compute_pre_type dbg e pre =
  print_dbg dbg "[> compute_pre_type";
  match safe_tc e pre with
  | None ->
    print_dbg dbg "safe_tc failed";
    PP_Unknown
  | Some ty ->
    print_dbg dbg "safe_tc succeeded";
    let brs, c = collect_arr_bs ty in
    print_dbg dbg ("num binders: " ^ string_of_int (List.Tot.length brs));
    match brs, is_total_or_gtotal c with
    | [], true ->
      print_dbg dbg "PP_Pure";
      PP_Pure
    | [b], true ->
      print_dbg dbg ("PP_State " ^ (term_to_string (type_of_binder b)));
      PP_State (type_of_binder b)
    | _ ->
      print_dbg dbg "PP_Unknown";
      PP_Unknown

val opt_remove_refin : typ -> Tac typ
let opt_remove_refin ty =
  match inspect ty with
  | Tv_Refine _ sort _ -> sort
  | _ -> ty

val compute_post_type : bool -> env -> term -> term -> Tac pre_post_type
let compute_post_type dbg e ret_type post =
  print_dbg dbg "[> compute_post_type";
  let get_tot_ret_type c : Tac (option term_view) =
    match get_total_or_gtotal_ret_type c with
    | Some ret_ty -> Some (inspect ret_ty)
    | None -> None
  in
  match safe_tc e post with
  | None ->
    print_dbg dbg "safe_tc failed";
    PP_Unknown
  | Some ty ->
    print_dbg dbg "safe_tc succeeded";
    let brs, c = collect_arr_bs ty in
    print_dbg dbg ("num binders: " ^ string_of_int (List.Tot.length brs));
    match brs, is_total_or_gtotal c with
    | [r], true ->
      (* Pure *)
      print_dbg dbg "PP_Pure";
      PP_Pure
    | [s1; r; s2], true ->
      (* Stateful: check that the state types are coherent *)
      let r_ty = type_of_binder r in
      let s1_ty = type_of_binder s1 in
      (* After testing with Stack: the final state seems to have a refinement
       * (which gives the postcondition) so we need to remove it to match
       * it against the initial state *)
      let s2_ty = opt_remove_refin (type_of_binder s2) in
      let ret_type_eq = term_eq ret_type r_ty in
      let state_type_eq = term_eq s1_ty s2_ty in
      print_dbg dbg ("- ret type:\n-- target: " ^ term_to_string ret_type ^
                     "\n-- binder: " ^ term_to_string r_ty);
      print_dbg dbg ("- state types:\n-- binder1: " ^ term_to_string s1_ty ^
                     "\n-- binder2: " ^ term_to_string s2_ty);
      print_dbg dbg ("- ret type equality: " ^ string_of_bool ret_type_eq);
      print_dbg dbg ("- state types equality: " ^ string_of_bool state_type_eq);
      if ret_type_eq && state_type_eq
      then
        begin
        print_dbg dbg ("PP_State" ^ term_to_string (type_of_binder s1));
        PP_State (type_of_binder s1)
        end
      else
        begin
        print_dbg dbg "PP_Unknown";
        PP_Unknown
        end
    | _ ->
      print_dbg dbg "PP_Unknown";
      PP_Unknown

val check_pre_post_type : bool -> env -> term -> term -> term -> Tac pre_post_type
let check_pre_post_type dbg e pre ret_type post =
  print_dbg dbg "[> check_pre_post_type";
  match compute_pre_type dbg e pre, compute_post_type dbg e ret_type post with
  | PP_Pure, PP_Pure ->
    print_dbg dbg "PP_Pure, PP_Pure";
    PP_Pure
  | PP_State ty1, PP_State ty2 ->
    print_dbg dbg "PP_State, PP_State";
    if term_eq ty1 ty2 then PP_State ty1 else PP_Unknown
  | _ ->
    print_dbg dbg "_, _";
    PP_Unknown

val check_opt_pre_post_type : bool -> env -> option term -> term -> option term -> Tac (option pre_post_type)
let check_opt_pre_post_type dbg e opt_pre ret_type opt_post =
  print_dbg dbg "[> check_opt_pre_post_type";
  match opt_pre, opt_post with
  | Some pre, Some post ->
    print_dbg dbg "Some pre, Some post";
    Some (check_pre_post_type dbg e pre ret_type post)
  | Some pre, None ->
    print_dbg dbg "Some pre, None";
    Some (compute_pre_type dbg e pre)
  | None, Some post ->
    print_dbg dbg "None, Some post";
    Some (compute_post_type dbg e ret_type post)
  | None, None ->
    print_dbg dbg "None, None";
    None

val _introduce_variables_for_abs : genv -> typ -> Tac (list term & list binder & genv)
let rec _introduce_variables_for_abs ge ty =
  match inspect ty with
  | Tv_Arrow b c ->
    let ge1, b1 = genv_push_fresh_binder ge ("__" ^ name_of_binder b) (type_of_binder b) in
    let bv1 = bv_of_binder b1 in
    let v1 = pack (Tv_Var bv1) in
    begin match get_total_or_gtotal_ret_type c with
    | Some ty1 ->
      let vl, bl, ge2 = _introduce_variables_for_abs ge1 ty1 in
      v1 :: vl, b1 :: bl, ge2
    | None -> [v1], [b1], ge1
    end
 | _ -> [], [], ge

val introduce_variables_for_abs : genv -> term -> Tac (list term & list binder & genv)
let introduce_variables_for_abs ge tm =
  match safe_tc ge.env tm with
  | Some ty -> _introduce_variables_for_abs ge ty
  | None -> [], [], ge

val introduce_variables_for_opt_abs : genv -> option term -> Tac (list term & list binder & genv)
let introduce_variables_for_opt_abs ge opt_tm =
  match opt_tm with
  | Some tm -> introduce_variables_for_abs ge tm
  | None -> [], [], ge


val effect_type_is_stateful : effect_type -> Tot bool
let effect_type_is_stateful etype =
  match etype with
  | E_Total | E_GTotal | E_Lemma | E_PURE | E_Pure -> false
  | E_Stack | E_ST | E_Unknown -> true

let is_st_get dbg t : Tac bool =
  print_dbg dbg ("[> is_st_get:\n" ^ term_to_string t);
  match inspect t with
  | Tv_App  hd (a, qual) ->
    print_dbg dbg "-> Is Tv_App";
    begin match inspect hd with
    | Tv_FVar fv ->
      print_dbg dbg ("-> Head is Tv_FVar: " ^ fv_to_string fv);
      fv_eq_name fv ["FStar"; "HyperStack"; "ST"; "get"]
    | _ ->
      print_dbg dbg "-> Head is not Tv_FVar";
      false
    end
  | _ ->
    print_dbg dbg "-> Is not Tv_App";
    false

let is_let_st_get dbg (t : term_view) =
  print_dbg dbg ("[> is_let_st_get:\n" ^ term_to_string t);
  match t with
  | Tv_Let recf attrs bv ty def body ->
    print_dbg dbg "The term is a let expression";
    if is_st_get dbg def then Some (bv, ty) else None
  | _ ->
    print_dbg dbg "The term is not a let expression";
    None

// TODO: Define relation between parents and children in and use it in explore_term
// app: head or arg
// let : bv or def or child
// match: scrutinee or branch
// ascribed: e or ty

/// Check if a term's computation is effectful. The return type is option
/// because we may not be able to retrieve the term computation.
val term_has_effectful_comp : bool -> env -> term -> Tac (option bool)
let term_has_effectful_comp dbg e tm =
  print_dbg dbg "[> term_has_effectful_comp";
  let einfo_opt = compute_effect_info dbg e tm in
  match einfo_opt with
  | Some einfo ->
    print_dbg dbg ("Effect type: " ^ effect_type_to_string einfo.ei_type);
    Some (not (effect_type_is_pure einfo.ei_type))
  | None ->
    print_dbg dbg "Could not compute effect info";
    None

/// Check if a related term is effectful. This is used to look for instances of
/// ``HS.mem`` to instantiate pre/postconditions, which means that the term should
/// be a parent/child term of the term under study, as generated by ``explore_term``
/// (otherwise the way we check that a term is effectful doesn't make sense).
/// The computation is an overapproximation: it may happen that, for instance, we
/// can't compute a term computation. In this case, we consider that the term is
/// effectful. There are also situations in which we may not be sure which term to
/// consider.
let related_term_is_effectul dbg ge tv : Tac bool =
  let is_effectful tm =
    term_has_effectful_comp dbg ge.env tm <> Some false
  in
  match tv with
  | Tv_Var _ | Tv_BVar _ | Tv_FVar _ -> false
  | Tv_App hd (a, qual) ->
    (* The term under focus should be the app itself or an argument *)
    false
  | Tv_Abs br body -> false
  | Tv_Arrow br c0 -> false
  | Tv_Type _ -> false
  | Tv_Refine bv sort ref ->
    false
  | Tv_Const _ -> false
  | Tv_Uvar _ _ -> false
  | Tv_Let recf attrs bv ty def body -> is_effectful def
  | Tv_Match scrutinee _ret_opt branches ->
    (* TODO: we need to keep track of the relation between parents and children *)
    (* We assume the term under focus is in one the branches of the match - this
     * assumption is safe: in the worst case, we won't be able to find a mem to use.
     * Besides, in practice it is uncommon (impossible?) to use an effectful term
     * as the scrutinee of a match *)
    is_effectful scrutinee
  | Tv_AscribedT e ty tac _ -> false (* The focused term should be inside the ascription *)
  | Tv_AscribedC e c tac _ -> false (* The focused term should be inside the ascription *)
  | _ -> (* Unknown: keep things safe *) true

/// Look for a term of the form ``let h = ST.get ()`` in a list of parent/children terms
/// and return the let-bound bv. Abort the search if we find a non-effectful term.
/// The typical usages of this function are the following:
/// - look for a state variable to instantiate the precondition of the term under focus
/// - look for state variables for the pre/postconditions of a term defined before
///   the term under focus.
val find_mem_in_related:
     dbg:bool
  -> ge:genv
  -> tms:list term_view
  -> Tac (option (bv & typ))

let rec find_mem_in_related dbg ge tms =
  match tms with
  | [] -> None
  | tv :: tms' ->
    print_dbg dbg ("[> find_mem_in_related:\n" ^ term_to_string tv);
    match is_let_st_get dbg tv with
    | Some bvt ->
      print_dbg dbg "Term is of the form `let x = FStar.HyperStack.ST.get ()`: success";
      Some bvt
    | None ->
      print_dbg dbg "Term is not of the form `let x = FStar.HyperStack.ST.get ()`: continuing";
      if related_term_is_effectul dbg ge tv
      then
        begin
        print_dbg dbg "Term is effectful: stopping here";
        None
        end
      else
        begin
        print_dbg dbg "Term is not effectful: continuing";
        find_mem_in_related dbg ge tms'
        end

// TODO: not used for now
/// Look for a term of the form ``let h = ST.get ()`` in a child term (the
/// focused term is supposed to be a subterm of the definition of a let-construct).
val find_mem_in_children:
     dbg:bool
  -> ge:genv
  -> child:term
  -> Tac (genv & option bv)

let rec find_mem_in_children dbg ge child =
  (* We stop whenever we find an expression which is not a let-binding *)
  match inspect child with
  | Tv_Let recf attrs bv ty def body ->
    if is_st_get dbg def then ge, Some bv
    else if term_has_effectful_comp dbg ge.env def <> Some false then ge, None
    else
      let ge1 = genv_push_bv ge bv ty false None in
      find_mem_in_children dbg ge1 body
  | _ -> ge, None

/// Instantiates optional pre and post conditions
val pre_post_to_propositions :
     dbg:bool
  -> ge:genv
  -> etype:effect_type
  -> ret_value:term
  -> ret_abs_binder:option binder
  -> ret_type:type_info
  -> opt_pre:option term
  -> opt_post:option term
  -> parents:list term_view (* to look for state variables for the pre *)
  -> children:list term_view (* to look for state variables for the pre and post *)
  -> Tac (genv & option proposition & option proposition)

let pre_post_to_propositions dbg ge0 etype v ret_abs_binder ret_type opt_pre opt_post
                             parents children =
  print_dbg dbg "[> pre_post_to_propositions: begin";
  print_dbg dbg ("- uninstantiated pre: " ^ option_to_string term_to_string opt_pre);
  print_dbg dbg ("- uninstantiated post: " ^ option_to_string term_to_string opt_post);
  let brs = match ret_abs_binder with | None -> [] | Some b -> [b] in
  (* Analyze the pre and the postcondition and introduce the necessary variables *)
  let ge3, (pre_values, pre_binders), (post_values, post_binders) =
    match etype with
    | E_Lemma ->
      print_dbg dbg "E_Lemma";
      ge0, ([], []), ([(`())], [])
    | E_Total | E_GTotal ->
      print_dbg dbg "E_Total/E_GTotal";
      ge0, ([], []), ([], [])
    | E_PURE | E_Pure ->
      print_dbg dbg "E_PURE/E_Pure";
      ge0, ([], []), ([v], brs)
    | E_Stack | E_ST ->
      print_dbg dbg "E_Stack/E_ST";
      (* Look for state variables in the context *)
      print_dbg dbg "Looking for the initial state in the context";
      let b1_opt = find_mem_in_related dbg ge0 parents in
      print_dbg dbg "Looking for the final state in the context";
      let b2_opt = find_mem_in_related dbg ge0 children in
      (* Introduce state variables if necessary *)
      let opt_push_fresh_state opt_bvt basename ge : Tac (term & binder & genv) =
        match opt_bvt with
        | Some (bv, ty) -> pack (Tv_Var bv), mk_binder bv ty, ge
        | None -> genv_push_fresh_var ge basename (`HS.mem)
      in
      let h1, b1, ge1 = opt_push_fresh_state b1_opt "__h0_" ge0 in
      let h2, b2, ge2 = opt_push_fresh_state b2_opt "__h1_" ge1 in
      ge2, ([h1], [b1]), ([h1; v; h2], List.Tot.flatten ([b1]::brs::[[b2]]))
    | E_Unknown ->
      (* We don't know what the effect is and the current pre and post-conditions
       * are currently guesses. Introduce any necessary variable abstracted by
       * those parameters *)
       (* The pre and post-conditions are likely to have the same shape as
        * one of Pure or Stack (depending on whether we use or not an internal
        * state). We try to check that and to instantiate them accordingly *)
      let pp_type = check_opt_pre_post_type dbg ge0.env opt_pre ret_type.ty opt_post in
      begin match pp_type with
      | Some PP_Pure ->
        print_dbg dbg "PP_Pure";
        (* We only need the return value *)
        ge0, ([], []), ([v], brs)
      | Some (PP_State state_type) ->
        print_dbg dbg "PP_State";
        (* Introduce variables for the states *)
        let s1, b1, s2, b2, ge1 = genv_push_two_fresh_vars ge0 "__s" state_type in
        ge1, ([s1], [b1]), ([s1; v; s2], List.Tot.flatten ([b1]::brs::[[b2]]))
      | Some PP_Unknown ->
        print_dbg dbg "PP_Unknown";
        (* Introduce variables for all the values, for the pre and the post *)
        let pre_values, pre_binders, ge1 = introduce_variables_for_opt_abs ge0 opt_pre in
        let post_values, post_binders, ge1 = introduce_variables_for_opt_abs ge1 opt_post in
        ge1, (pre_values, pre_binders), (post_values, post_binders)
      | _ ->
        print_dbg dbg "No pre and no post";
        (* No pre and no post *)
        ge0, ([], []), ([], [])
      end
  in
  (* Generate the propositions: *)
  (* - from the precondition *)
  let pre_prop = opt_mk_app_norm ge3.env opt_pre pre_values in
  (* - from the postcondition - note that in the case of a global post-condition
   *   we might try to instantiate the return variable with a variable whose
   *   type is not correct, leading to an error. We thus catch errors below and
   *   drop the post if there is a problem *)
  let post_prop =
    try opt_mk_app_norm ge3.env opt_post post_values
    with
    | _ ->
      print_dbg dbg "Dropping a postcondition because of incoherent typing";
      None
  in
  (* return *)
  print_dbg dbg "[> pre_post_to_propositions: end";
  ge3, pre_prop, post_prop

/// Convert effectful type information to a list of propositions. May have to
/// introduce additional binders for the preconditions/postconditions/goal (hence
/// the environment in the return type).
/// The ``bind_var`` parameter is a variable if the studied term was bound in a let
/// expression.
val eterm_info_to_assertions :
     dbg:bool
  -> with_gpre:bool
  -> with_gpost:bool
  -> ge:genv
  -> t:term
  -> is_let:bool (* the term is the bound expression in a let binding *)
  -> is_assert:bool (* the term is an assert - in which case we only output the precondition *)
  -> info:eterm_info
  -> opt_bind_var:option term (* if let binding: the bound var *)
  -> opt_c:option typ_or_comp
  -> parents:list term_view
  -> children:list term_view ->
  Tac (genv & assertions)

let eterm_info_to_assertions dbg with_gpre with_gpost ge t is_let is_assert info bind_var opt_c
                             parents children =
  print_dbg dbg "[> eterm_info_to_assertions";
  (* Introduce additional variables to instantiate the return type refinement,
   * the precondition, the postcondition and the goal *)
  (* First, the return value: returns an updated env, the value to use for
   * the return type and a list of abstract binders *)
  let einfo = info.einfo in
  let ge0, (v : term), (opt_b : option binder) =
    match bind_var with
    | Some v -> ge, v, None
    | None ->
      (* If the studied term is stateless, we can use it directly in the
       * propositions. If the return value is of type unit, we can just use ().
       * Otherwise we need to introduce a variable.
       * For the reason why we do this: remember that the studied term might be
       * a return value: it is not necessarily bound in a let. *)
      if effect_type_is_stateful einfo.ei_type then
        if is_unit_type einfo.ei_ret_type.ty then
          ge, `(), None
        else
          let b = fresh_binder ge.env "__ret" einfo.ei_ret_type.ty in
          let bv = bv_of_binder b in
          let tm = pack (Tv_Var bv) in
          genv_push_binder ge b true None, tm, Some b
      else ge, t, None
  in
  (* Generate propositions from the pre and the post-conditions *)
  (**) print_dbg dbg "> Instantiating local pre/post";
  let ge1, pre_prop, post_prop =
    pre_post_to_propositions dbg ge0 einfo.ei_type v opt_b einfo.ei_ret_type
                             einfo.ei_pre einfo.ei_post parents children in
  print_dbg dbg ("- pre prop: " ^ option_to_string term_to_string pre_prop);
  print_dbg dbg ("- post prop: " ^ option_to_string term_to_string post_prop);
  (* If the term is an assertion/assumption, only output the postcondition -
   * note that in the case of an assertion, the pre and the post are the same,
   * but in the case of an assumption, only the post is interesting *)
  if is_assert then
    begin
    print_dbg dbg "The term is an assert: only keep the postcondition";
    ge1, { pres = opt_cons post_prop []; posts = [] }
    end
  else begin
    (* Generate propositions from the target computation (pre, post, type cast) *)
    let ge2, gparams_props, gpre_prop, gcast_props, gpost_prop =
      (* Check if we do the computation (which can be expensive) - note that
       * computing the global postcondition makes sense only if the focused
       * term is the return value and thus not a let-binding *)
      let with_goal : bool = with_gpre || ((not is_let) && with_gpost) in
      begin match opt_c, with_goal with
      | Some c, true ->
        let ei = typ_or_comp_to_effect_info dbg ge1 c in
        print_dbg dbg ("- target effect: " ^ effect_info_to_string ei);
        print_dbg dbg ("- global unfilt. pre: " ^ option_to_string term_to_string ei.ei_pre);
        print_dbg dbg ("- global unfilt. post: " ^ option_to_string term_to_string ei.ei_post);
        (* The parameters' type information. To be used only if the variables are not
         * shadowed (the parameters themselves, but also the variables inside the refinements) *)
        let gparams_props =
          begin
          if with_gpre then
            begin
            print_dbg dbg "Generating assertions from the global parameters' types";
            print_dbg dbg ("Current genv:\n" ^ genv_to_string ge1);
            (* Retrieve the types and pair them with the parameters - note that
             * we need to reverse the list of parameters (the outer parameter was
             * added first in the list and is thus last) *)
            let params =
              rev (List.Tot.map (fun x -> (x, type_of_binder x)) (params_of_typ_or_comp c)) in
            iteri (fun i (b, _) -> print_dbg dbg ("Global parameter " ^ string_of_int i ^
                                        ": " ^ binder_to_string b)) params;
            (* Filter the shadowed parameters *)
            let params = filter (fun (b, _)-> not (binder_is_shadowed ge1 b)) params in
            (* Generate the propositions *)
            let param_to_props (x : (binder & typ)) : Tac (list term) =
              let b, ty = x in
              let bv = bv_of_binder b in
              print_dbg dbg ("Generating assertions from global parameter: " ^ binder_to_string b);
              let tinfo = get_type_info_from_type ty in
              let v = pack (Tv_Var bv) in
              let p1 = mk_has_type v tinfo.ty in
              let pl = match tinfo.refin with
              | None -> []
              | Some r ->
                let p2 = mk_app_norm ge1.env r [v] in
                (* Discard the proposition generated from the type refinement if
                 * it contains shadowed variables *)
                if term_has_shadowed_variables ge1 p2
                then begin print_dbg dbg "Discarding type refinement because of shadowed variables"; [] end
                else begin print_dbg dbg "Keeping type refinement"; [p2] end
              in
              p1 :: pl
            in
            let props = map param_to_props params in
            List.Tot.flatten props
            end
          else
            begin
            print_dbg dbg "Ignoring the global parameters' types";
            []
            end
          end <: Tac (list term)
        in
        (* The global pre-condition is to be used only if none of its variables
         * are shadowed (which implies that we are close enough to the top of
         * the function *)
        let gpre =
          match ei.ei_pre, with_gpre with
          | Some pre, true ->
            if term_has_shadowed_variables ge1 pre then
              begin
              print_dbg dbg "Dropping the global precondition because of shadowed variables";
              None
              end
            else ei.ei_pre
          | _ -> None
        in
        (* The global post-condition and the type cast are relevant only if the
         * studied term is not the definition in a let binding *)
        let gpost, gcast_props =
          if not with_gpost then None, []
          else if is_let then
            begin
            print_dbg dbg "Dropping the global postcondition and return type because we are studying a let expression";
            None, []
            end
          else
            (* Because of the way the studied function is rewritten before being sent to F*
             * we might have a problem with the return type (we might instantiate
             * the return variable from the global post or from the return type
             * refinement with a variable whose type is not valid for that, triggering
             * an exception. In that case, we drop the post and the target type
             * refinement. Note that here only the type refinement may be instantiated,
             * we thus also need to check for the post inside ``pre_post_to_propositions`` *)
            try
              print_dbg dbg "> Generating propositions from the global type cast";
              print_dbg dbg ("- known type: " ^ type_info_to_string einfo.ei_ret_type);
              print_dbg dbg ("- exp. type : " ^ type_info_to_string ei.ei_ret_type);
              let gcast = mk_cast_info v (Some einfo.ei_ret_type) (Some ei.ei_ret_type) in
              print_dbg dbg (cast_info_to_string gcast);
              let gcast_props = cast_info_to_propositions dbg ge1 gcast in
              print_dbg dbg "> Propositions for global type cast:";
              print_dbg dbg (list_to_string term_to_string gcast_props);
              ei.ei_post, List.Tot.rev gcast_props
            with
            | _ ->
              print_dbg dbg "Dropping the global postcondition and return type because of incoherent typing";
              None, []
        in
        (* Generate the propositions from the precondition and the postcondition *)
        (* TODO: not sure about the return type parameter: maybe catch failures *)
        print_dbg dbg "> Instantiating global pre/post";
        (* Note that we need to revert the lists of parents terms *)
        (* For the children:
         * - if the focused term is the return value and is pure: go look for
         *   a state variable introduced before
         * - otherwise, use the children in revert order *)
        let gchildren =
          if is_let then rev children (* the postcondition should have been dropped anyway *)
          else if effect_type_is_stateful einfo.ei_type then rev children
          else parents
        in
        let ge2, gpre_prop, gpost_prop =
          pre_post_to_propositions dbg ge1 ei.ei_type v opt_b einfo.ei_ret_type
                                   gpre gpost (rev parents) gchildren in
        (* Some debugging output *)
        print_dbg dbg ("- global pre prop: " ^ option_to_string term_to_string gpre_prop);
        print_dbg dbg ("- global post prop: " ^ option_to_string term_to_string gpost_prop);
        (* Return type: *)
        ge2, gparams_props, gpre_prop, gcast_props, gpost_prop
      | _, _ ->
        ge1, [], None, [], None
      end <: Tac _
    in
    (* Generate the propositions: *)
    (* - from the parameters' cast info *)
    let params_props = cast_info_list_to_propositions dbg ge2 info.parameters in
    (* - from the return type *)
    let (ret_values : list term), (ret_binders : list binder) =
      if E_Lemma? einfo.ei_type then ([] <: list term), ([] <: list binder)
      else [v], (match opt_b with | Some b -> [b] | None -> []) in
    let ret_has_type_prop =
      match ret_values with
      | [v] -> Some (mk_has_type v einfo.ei_ret_type.ty)
      | _ -> None
    in
    let ret_refin_prop = opt_mk_app_norm ge2.env (get_opt_refinment einfo.ei_ret_type) ret_values in
    (* Concatenate, revert and return *)
    let pres = opt_cons gpre_prop (List.Tot.append params_props (opt_cons pre_prop [])) in
    let pres = append gparams_props pres in
    let posts = opt_cons ret_has_type_prop
                (opt_cons ret_refin_prop (opt_cons post_prop
                 (List.Tot.append gcast_props (opt_cons gpost_prop [])))) in
    (* Debugging output *)
    print_dbg dbg "- generated pres:";
    if dbg then iter (fun x -> print (term_to_string x)) pres;
    print_dbg dbg "- generated posts:";
    if dbg then iter (fun x -> print (term_to_string x)) posts;
    ge2, { pres = pres; posts = posts }
    end
