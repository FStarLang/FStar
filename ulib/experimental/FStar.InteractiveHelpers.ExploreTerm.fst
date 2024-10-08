module FStar.InteractiveHelpers.ExploreTerm

open FStar.List.Tot
open FStar.Tactics
open FStar.Mul
open FStar.InteractiveHelpers.Base

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(*** Types and effects *)
/// Define utilities to handle and carry types and effects

(**** Type analysis *)
/// Retrieve and deconstruct a type/effect

/// Some constants
//let prims_true_qn = "Prims.l_True"
//let prims_true_term = `Prims.l_True

let pure_effect_qn = "Prims.PURE"
let pure_hoare_effect_qn = "Prims.Pure"
let stack_effect_qn = "FStar.HyperStack.ST.Stack"
let st_effect_qn = "FStar.HyperStack.ST.ST"


/// Return the qualifier of a comp as a string
val comp_qualifier (c : comp) : Tac string

#push-options "--ifuel 1"
let comp_qualifier (c : comp) : Tac string =
  match inspect_comp c with
  | C_Total _ -> "C_Total"
  | C_GTotal _ -> "C_GTotal"
  | C_Lemma _ _ _ -> "C_Lemma"
  | C_Eff _ _ _ _ _ -> "C_Eff"
#pop-options

/// Effect information: we list the current supported effects
type effect_type =
| E_Total | E_GTotal | E_Lemma | E_PURE | E_Pure | E_Stack | E_ST | E_Unknown

val effect_type_to_string : effect_type -> string

#push-options "--ifuel 1"
let effect_type_to_string ety =
  match ety with
  | E_Total -> "E_Total"
  | E_GTotal -> "E_GTotal"
  | E_Lemma -> "E_Lemma"
  | E_PURE -> "E_PURE"
  | E_Pure -> "E_Pure"
  | E_Stack -> "E_Stack"
  | E_ST -> "E_ST"
  | E_Unknown -> "E_Unknown"
#pop-options

val effect_name_to_type (ename : name) : Tot effect_type

let effect_name_to_type (ename : name) : Tot effect_type =
  let ename = flatten_name ename in
  if ename = pure_effect_qn then E_PURE
  else if ename = pure_hoare_effect_qn then E_Pure
  else if ename = stack_effect_qn then E_Stack
  else if ename = st_effect_qn then E_ST
  else E_Unknown

val effect_type_is_pure : effect_type -> Tot bool
let effect_type_is_pure etype =
  match etype with
  | E_Total | E_GTotal | E_Lemma | E_PURE | E_Pure -> true
  | E_Stack | E_ST | E_Unknown -> false

/// Type information
noeq type type_info = {
  ty : typ; (* the type without refinement *)
  refin : option term;
}

let mk_type_info = Mktype_info

val type_info_to_string : type_info -> Tac string
let type_info_to_string info =
  "Mktype_info (" ^
  term_to_string info.ty ^ ") (" ^
  option_to_string term_to_string info.refin ^ ")"

let unit_type_info = mk_type_info (`unit) None

val safe_tc (e:env) (t:term) : Tac (option term)
let safe_tc e t =
  try Some (tc e t) with | _ -> None

val safe_tcc (e:env) (t:term) : Tac (option comp)
let safe_tcc e t =
  try Some (tcc e t) with | _ -> None

let get_type_info_from_type (ty:typ) : Tac type_info =
  match inspect ty with
  | Tv_Refine bv sort refin ->
    let raw_type = prettify_term false sort  in
    let b : binder = mk_binder bv sort in
    let refin = prettify_term false refin in
    let refin = pack (Tv_Abs b refin) in
    mk_type_info raw_type (Some refin)
  | _ ->
    let ty = prettify_term false ty in
    mk_type_info ty None

#push-options "--ifuel 1"
let get_type_info (e:env) (t:term) : Tac (option type_info) =
  match safe_tc e t with
  | None -> None
  | Some ty -> Some (get_type_info_from_type ty)
#pop-options

val get_total_or_gtotal_ret_type : comp -> Tot (option typ)
let get_total_or_gtotal_ret_type c =
  match inspect_comp c with
  | C_Total ret_ty | C_GTotal ret_ty -> Some ret_ty
  | _ -> None

val get_comp_ret_type : comp -> Tot typ
let get_comp_ret_type c =
  match inspect_comp c with
  | C_Total ret_ty | C_GTotal ret_ty
  | C_Eff _ _ ret_ty _ _ -> ret_ty
  | C_Lemma _ _ _ -> (`unit)

val is_total_or_gtotal : comp -> Tot bool
let is_total_or_gtotal c =
  Some? (get_total_or_gtotal_ret_type c)

val is_unit_type : typ -> Tac bool
let is_unit_type ty =
  match inspect ty with
  | Tv_FVar fv -> fv_eq_name fv Reflection.Const.unit_lid
  | _ -> false


(**** typ_or_comp *)
/// This type is used to store typing information.
/// We use it mostly to track what the target type/computation is for a term,
/// while exploring this term. It is especially useful to generate post-conditions,
/// for example. We store the list of abstractions encountered so far at the
/// same time.
/// Note that in order to keep track of the type correctly, whenever we encounter
/// an abstraction in the term, we need to check that the term' type is an arrow,
/// in which case we need to do a substitution (the arrow takes as first parameter
/// which is not the same as the abstraction's binder). As the substitution is costly
/// (we do it by using the normalizer, but the "final" return term is the whole
/// function's body type, which is often super big) we do it lazily: we count how
/// many parameters we have encountered and not substituted, and "flush" when we
/// really need to inspect the typ_or_comp.
// TODO: actually we only need to carry a comp (if typ: consider it total)
(* TODO: remove the instantiation: instantiate incrementally *)
noeq type typ_or_comp =
| TC_Typ : v:typ -> pl:list binder -> num_unflushed:nat -> typ_or_comp
| TC_Comp : v:comp -> pl:list binder -> num_unflushed:nat -> typ_or_comp

let typ_or_comp_to_string (tyc : typ_or_comp) : Tac string =
  match tyc with
  | TC_Typ v pl num_unflushed ->
    "TC_Typ (" ^ term_to_string v ^ ") " ^ list_to_string (fun b -> name_of_binder b) pl ^
    " " ^ string_of_int num_unflushed
  | TC_Comp c pl num_unflushed ->
    "TC_Comp (" ^ acomp_to_string c ^ ") " ^ list_to_string (fun b -> name_of_binder b) pl ^
    " " ^ string_of_int num_unflushed

/// Return the list of parameters stored in a ``typ_or_comp``
let params_of_typ_or_comp (c : typ_or_comp) : list binder =
  match c with
  | TC_Typ _ pl _ | TC_Comp _ pl _ -> pl

let num_unflushed_of_typ_or_comp (c : typ_or_comp) : nat =
match c with
  | TC_Typ _ _ n | TC_Comp _ _ n -> n

/// Compute a ``typ_or_comp`` from the type of a term
// TODO: try to get a more precise comp
val safe_typ_or_comp : bool -> env -> term ->
                       Tac (opt:option typ_or_comp{Some? opt ==> TC_Comp? (Some?.v opt)})
let safe_typ_or_comp dbg e t =
  match safe_tcc e t with
  | None ->
    print_dbg dbg ("[> safe_typ_or_comp:" ^
                   "\n-term: " ^ term_to_string t ^
                   "\n-comp: None");
    None
  | Some c ->
    print_dbg dbg ("[> safe_typ_or_comp:" ^
                   "\n-term: " ^ term_to_string t ^
                   "\n-comp: " ^ acomp_to_string c);
    Some (TC_Comp c [] 0)

val subst_bv_in_comp : env -> bv -> typ -> term -> comp -> Tac comp
let subst_bv_in_comp e b sort t c =
  apply_subst_in_comp e c [((b, sort), t)]

val subst_binder_in_comp : env -> binder -> term -> comp -> Tac comp
let subst_binder_in_comp e b t c =
  subst_bv_in_comp e (bv_of_binder b) (binder_sort b) t c

/// Utility for computations: unfold a type until it is of the form Tv_Arrow _ _,
/// fail otherwise
val unfold_until_arrow : env -> typ -> Tac typ
let rec unfold_until_arrow e ty0 =
  if Tv_Arrow? (inspect ty0) then ty0
  else
    begin
    (* Start by normalizing the term - note that this operation is expensive *)
    let ty = norm_term_env e [] ty0 in
    (* Helper to unfold top-level identifiers *)
    let unfold_fv (fv : fv) : Tac term =
      let ty = pack (Tv_FVar fv) in
      let fvn = flatten_name (inspect_fv fv) in
      (* unfold the top level binding, check that it has changed, and recurse *)
      let ty' = norm_term_env e [delta_only [fvn]] ty in
      (* I'm not confident about using eq_term here *)
      begin match inspect ty' with
      | Tv_FVar fv' ->
        if flatten_name (inspect_fv fv') = fvn
        then mfail ("unfold_until_arrow: could not unfold: " ^ term_to_string ty0) else ty'
      | _ -> ty'
      end
    in
    (* Inspect *)
    match inspect ty with
    | Tv_Arrow _ _ -> ty
    | Tv_FVar fv ->
      (* Try to unfold the top-level identifier and recurse *)
      let ty' = unfold_fv fv in
      unfold_until_arrow e ty'
    | Tv_App _ _ ->
      (* Strip all the parameters, try to unfold the head and recurse *)
      let hd, args = collect_app ty in
      begin match inspect hd with
      | Tv_FVar fv ->
        let hd' = unfold_fv fv in
        let ty' = mk_app hd' args in
        unfold_until_arrow e ty'
      | _ -> mfail ("unfold_until_arrow: could not unfold: " ^ term_to_string ty0)
      end
    | Tv_Refine bv sort ref ->
      unfold_until_arrow e sort
    | Tv_AscribedT body _ _ _
    | Tv_AscribedC body _ _ _ ->
      unfold_until_arrow e body
    | _ ->
      (* Other situations: don't know what to do *)
      mfail ("unfold_until_arrow: could not unfold: " ^ term_to_string ty0)
    end

/// Instantiate a comp
val inst_comp_once : env -> comp -> term -> Tac comp
let inst_comp_once e c t =
  let ty = get_comp_ret_type c in
  let ty' = unfold_until_arrow e ty in
  begin match inspect ty' with
  | Tv_Arrow b1 c1 ->
    subst_binder_in_comp e b1 t c1
  | _ -> (* Inconsistent state *)
    mfail "inst_comp_once: inconsistent state"
  end

val inst_comp : env -> comp -> list term -> Tac comp
let rec inst_comp e c tl =
  match tl with
  | [] -> c
  | t :: tl' ->
    let c' = try inst_comp_once e c t
             with | MetaAnalysis msg -> mfail_doc ([text "inst_comp: error"] @ msg)
                  | err -> raise err
    in
    inst_comp e c' tl'

/// Update the current ``typ_or_comp`` before going into the body of an abstraction.
/// Explanations:
/// In the case we dive into a term of the form:
/// [> (fun x -> body) : y:ty -> body_type
/// we need to substitute y with x in body_type to get the proper type for body.
/// Note that we checked, and in practice the binders are indeed different.
// TODO: actually, we updated it to do a lazy instantiation
val abs_update_typ_or_comp : binder -> typ_or_comp -> env -> Tac typ_or_comp

let _abs_update_typ (b:binder) (ty:typ) (pl:list binder) (e:env) :
  Tac typ_or_comp =
  (* Try to reveal an arrow *)
  try
    let ty' = unfold_until_arrow e ty in
    begin match inspect ty' with
    | Tv_Arrow b1 c1 ->
      let c1' = subst_binder_in_comp e b1 (pack (Tv_Var (bv_of_binder b))) c1 in
      TC_Comp c1' (b :: pl) 0
    | _ -> (* Inconsistent state *)
      mfail "_abs_update_typ: inconsistent state"
    end
  with
  | MetaAnalysis msg ->
    mfail_doc (
      [text ("_abs_update_typ: could not find an arrow in " ^ term_to_string ty)]
      @ msg
    )
  | err -> raise err

let abs_update_typ_or_comp (b:binder) (c : typ_or_comp) (e:env) : Tac typ_or_comp =
  match c with
  (*| TC_Typ v pl n -> _abs_update_typ b v pl e
  | TC_Comp v pl n ->
    (* Note that the computation is not necessarily pure, in which case we might
     * want to do something with the effect arguments (pre, post...) - for
     * now we just ignore them *)
    let ty = get_comp_ret_type v in
    _abs_update_typ b ty pl e *)
  | TC_Typ v pl n -> TC_Typ v (b::pl) (n+1)
  | TC_Comp v pl n -> TC_Comp v (b::pl) (n+1)

val abs_update_opt_typ_or_comp : binder -> option typ_or_comp -> env ->
                                 Tac (option typ_or_comp)
let abs_update_opt_typ_or_comp b opt_c e =
  match opt_c with
  | None -> None
  | Some c ->
    try
      let c = abs_update_typ_or_comp b c e in
      Some c
    with | MetaAnalysis msg -> None
         | err -> raise err

/// Flush the instantiation stored in a ``typ_or_comp``
val flush_typ_or_comp : bool -> env -> typ_or_comp ->
                        Tac (tyc:typ_or_comp{num_unflushed_of_typ_or_comp tyc = 0})

/// Strip all the arrows we can without doing any instantiation. When we can't
/// strip arrows anymore, do the instantiation at once.
/// We keep track of two list of binders:
/// - the remaining binders
/// - the instantiation corresponding to the arrows we have stripped so far, and
///   which will be applied all at once
let rec _flush_typ_or_comp_comp (dbg : bool) (e:env) (rem : list binder) (inst : list ((bv & typ) & term))
                                (c:comp) : Tac comp =
  let flush c inst =
    let inst = List.Tot.rev inst in
    apply_subst_in_comp e c inst
  in
  match rem with
  | [] ->
    (* No more binders: flush *)
    flush c inst
  | b :: rem' ->
    (* Check if the return type is an arrow, if not flush and normalize *)
    let ty = get_comp_ret_type c in
    let ty, inst' =
      if Tv_Arrow? (inspect ty) then ty, inst
      else get_comp_ret_type (flush c inst), []
    in
    match inspect ty with
    | Tv_Arrow b' c' ->
      _flush_typ_or_comp_comp dbg e rem' (((bv_of_binder b', binder_sort b'), pack (Tv_Var (bv_of_binder b)))::inst) c'
    | _ ->
      mfail ("_flush_typ_or_comp: inconsistent state" ^
             "\n-comp: " ^ acomp_to_string c ^
             "\n-remaning binders: " ^ list_to_string (fun b -> name_of_binder b) rem)

let flush_typ_or_comp dbg e tyc =
  let flush_comp pl n c : Tac (tyc:typ_or_comp{num_unflushed_of_typ_or_comp tyc = 0})  =
    let pl', _ = List.Tot.splitAt n pl in
    let pl' = List.Tot.rev pl' in
    let c = _flush_typ_or_comp_comp dbg e pl' [] c in
    TC_Comp c pl 0
  in
  try begin match tyc with
  | TC_Typ ty pl n ->
    let c = pack_comp (C_Total ty) in
    flush_comp pl n c
  | TC_Comp c pl n -> flush_comp pl n c
  end
  with | MetaAnalysis msg ->
         mfail_doc ([text ("flush_typ_or_comp failed on: " ^ typ_or_comp_to_string tyc)] @  msg)
       | err -> raise err

/// Compute the target ``typ_or_comp`` for an argument by the type of the head:
/// in `hd a`, if `hd` has type `t -> ...`, use `t`
val safe_arg_typ_or_comp : bool -> env -> term ->
                           Tac (opt:option typ_or_comp{Some? opt ==> TC_Typ? (Some?.v opt)})
let safe_arg_typ_or_comp dbg e hd =
  print_dbg dbg ("safe_arg_typ_or_comp: " ^ term_to_string hd);
  match safe_tc e hd with
  | None -> None
  | Some ty ->
    print_dbg dbg ("hd type: " ^ term_to_string ty);
    let ty =
      if Tv_Arrow? (inspect ty) then
        begin
        print_dbg dbg "no need to unfold the type";
        ty
        end
      else
        begin
        print_dbg dbg "need to unfold the type";
        let ty = unfold_until_arrow e ty in
        print_dbg dbg ("result of unfolding : "^ term_to_string ty);
        ty
        end
    in
    match inspect ty with
    | Tv_Arrow b c -> Some (TC_Typ (type_of_binder b) [] 0)
    | _ -> None

/// Exploring a term

(*** Term exploration *)
/// Explore a term, correctly updating the environment when traversing abstractions

let convert_ctrl_flag (flag : ctrl_flag) =
  match flag with
  | Continue -> Continue
  | Skip -> Continue
  | Abort -> Abort

/// TODO: for now I need to use universe 0 for type a because otherwise it doesn't
/// type check
/// ctrl_flag:
/// - Continue: continue exploring the term
/// - Skip: don't explore the sub-terms of this term
/// - Abort: stop exploration
/// TODO: we might want a more precise control (like: don't explore the type of the
/// ascription but explore its body)
/// Note that ``explore_term`` doesn't use the environment parameter besides pushing
/// binders and passing it to ``f``, which means that you can give it arbitrary
/// environments, ``explore_term`` itself won't fail (but the passed function might).

let explorer (a : Type) =
  a -> genv -> list (genv & term_view) -> option typ_or_comp -> term_view ->
  Tac (a & ctrl_flag)

// TODO: use more
let bind_expl (#a : Type) (x : a) (f1 f2 : a -> Tac (a & ctrl_flag)) : Tac (a & ctrl_flag) =
  let x1, flag1 = f1 x in
  if flag1 = Continue then
    f2 x1
  else x1, convert_ctrl_flag flag1  

// TODO: change the signature to move the dbg flag
val explore_term :
     dbg : bool
  -> dfs : bool (* depth-first search *)
  -> #a : Type0
  -> f : explorer a
  -> x : a
  -> ge : genv
  (* the list of terms traversed so far (first is most recent) with the environment
   * at the time they were traversed *)
  -> parents : list (genv & term_view)
  -> c : option typ_or_comp
  -> t:term ->
  Tac (a & ctrl_flag)

val explore_pattern :
     dbg : bool
  -> dfs : bool (* depth-first search *)
  -> #a : Type0
  -> f : explorer a
  -> x : a
  -> ge:genv
  -> pat:pattern ->
  Tac (genv & a & ctrl_flag)

(* TODO: carry around the list of encompassing terms *)
let rec explore_term dbg dfs #a f x ge0 pl0 c0 t0 =
  print_dbg dbg ("[> explore_term: " ^ term_construct t0 ^ ":\n" ^ term_to_string t0);
  let tv0 = inspect t0 in
  let x0, flag = f x ge0 pl0 c0 tv0 in
  let pl1 = (ge0, tv0) :: pl0 in
  if flag = Continue then
    begin match tv0 with
    | Tv_Var _ | Tv_BVar _ | Tv_FVar _ -> x0, Continue
    | Tv_App hd (a,qual) ->
      (* Explore the argument - we update the target typ_or_comp when doing so.
       * Note that the only way to get the correct target type is to deconstruct
       * the type of the head *)
      let a_c = safe_arg_typ_or_comp dbg ge0.env hd in
      print_dbg dbg ("Tv_App: updated target typ_or_comp to:\n" ^
                     option_to_string typ_or_comp_to_string a_c);
      let x1, flag1 = explore_term dbg dfs f x0 ge0 pl1 a_c a in
      (* Explore the head - no type information here: we can compute it,
       * but it seems useless (or maybe use it only if it is not Total) *)
      if flag1 = Continue then
        explore_term dbg dfs f x1 ge0 pl1 None hd
      else x1, convert_ctrl_flag flag1
    | Tv_Abs br body ->
      let ge1 = genv_push_binder ge0 br false None in
      let c1 = abs_update_opt_typ_or_comp br c0 ge1.env in
      explore_term dbg dfs f x0 ge1 pl1 c1 body
    | Tv_Arrow br c0 -> x0, Continue (* TODO: we might want to explore that *)
    | Tv_Type _ -> x0, Continue
    | Tv_Refine bv sort ref ->
      let bvv = inspect_bv bv in
      let x1, flag1 = explore_term dbg dfs f x0 ge0 pl1 None sort in
      if flag1 = Continue then
        let ge1 = genv_push_bv ge0 bv sort false None in
        explore_term dbg dfs f x1 ge1 pl1 None ref
      else x1, convert_ctrl_flag flag1
    | Tv_Const _ -> x0, Continue
    | Tv_Uvar _ _ -> x0, Continue
    | Tv_Let recf attrs bv ty def body ->
      (* Binding definition exploration - for the target computation: initially we
       * used the type of the definition, however it is often unnecessarily complex.
       * Now, we use the type of the binder used for the binding. *)
      let def_c = Some (TC_Typ ty [] 0) in
      let explore_def x = explore_term dbg dfs f x ge0 pl1 def_c def in
      (* Exploration of the following instructions *)
      let ge1 = genv_push_bv ge0 bv ty false (Some def) in
      let explore_next x = explore_term dbg dfs f x ge1 pl1 c0 body in
      (* Perform the exploration in the proper order *)
      let expl1, expl2 = if dfs then explore_next, explore_def else explore_def, explore_next in
      bind_expl x0 expl1 expl2
    | Tv_Match scrutinee _ret_opt branches ->  //AR: TODO: need to account for returns annotation here
      (* Auxiliary function to explore the branches *)
      let explore_branch (x_flag : a & ctrl_flag) (br : branch) : Tac (a & ctrl_flag)=
        let x0, flag = x_flag in
        if flag = Continue then
          let pat, branch_body = br in
          (* Explore the pattern *)
          let ge1, x1, flag1 = explore_pattern dbg dfs #a f x0 ge0 pat in
          if flag1 = Continue then
            (* Explore the branch body *)
            explore_term dbg dfs #a f x1 ge1 pl1 c0 branch_body
          else x1, convert_ctrl_flag flag1
        (* Don't convert the flag *)
        else x0, flag
      in
      (* Explore the scrutinee *)
      let scrut_c = safe_typ_or_comp dbg ge0.env scrutinee in
      let x1 = explore_term dbg dfs #a f x0 ge0 pl1 scrut_c scrutinee in
      (* Explore the branches *)
      fold_left explore_branch x1 branches
    | Tv_AscribedT e ty tac _ ->
      let c1 = Some (TC_Typ ty [] 0) in
      let x1, flag = explore_term dbg dfs #a f x0 ge0 pl1 None ty in
      if flag = Continue then
        explore_term dbg dfs #a f x1 ge0 pl1 c1 e
      else x1, convert_ctrl_flag flag
    | Tv_AscribedC e c1 tac _ ->
      (* TODO: explore the comp *)
      explore_term dbg dfs #a f x0 ge0 pl1 (Some (TC_Comp c1 [] 0)) e
    | _ ->
      (* Unknown *)
      x0, Continue
    end
  else x0, convert_ctrl_flag flag

and explore_pattern dbg dfs #a f x ge0 pat =
  print_dbg dbg ("[> explore_pattern:");
  match pat with
  | Pat_Constant _ -> ge0, x, Continue
  | Pat_Cons fv us patterns ->
    let explore_pat ge_x_flag pat =
      let ge0, x, flag = ge_x_flag in
      let pat1, _ = pat in
      if flag = Continue then
        explore_pattern dbg dfs #a f x ge0 pat1
      else
        (* Don't convert the flag *)
        ge0, x, flag
    in
    fold_left explore_pat (ge0, x, Continue) patterns
  | Pat_Var bv st ->
    let ge1 = genv_push_bv ge0 bv (unseal st) false None in
    ge1, x, Continue
  | Pat_Dot_Term _ -> ge0, x, Continue

(*** Variables in a term *)
/// Returns the list of free variables contained in a term
val free_in : term -> Tac (list bv)
let free_in t =
  let same_name (bv1 bv2 : bv) : Tac bool =
    name_of_bv bv1 = name_of_bv bv2
  in
  let update_free (fl:list bv) (ge:genv) (pl:list (genv & term_view))
                  (c:option typ_or_comp) (tv:term_view) :
    Tac (list bv & ctrl_flag) =
    match tv with
    | Tv_Var bv | Tv_BVar bv ->
      (* Check if the binding was not introduced during the traversal *)
      begin match genv_get_from_name ge (name_of_bv bv) with
      | None ->
        (* Check if we didn't already count the binding *)
        let fl' = if Tactics.tryFind (same_name bv) fl then fl else bv :: fl in
        fl', Continue
      | Some _ -> fl, Continue
      end
    | _ -> fl, Continue
  in
  let e = top_env () in (* we actually don't care about the environment *)
  let ge = mk_genv e [] [] in
  List.Tot.rev (fst (explore_term false false update_free [] ge [] None t))

/// Returns the list of abstract variables appearing in a term, in the order in
/// which they were introduced in the context.
val abs_free_in : genv -> term -> Tac (list (bv & typ))
let abs_free_in ge t =
  let fvl = free_in t in
  let absl = List.Tot.rev (genv_abstract_bvs ge) in
  let is_free_in_term bv =
    Some? (List.Tot.find (bv_eq bv) fvl)
  in
  let absfree = List.Tot.concatMap
    (fun (bv, ty) -> if is_free_in_term bv then [bv,ty] else []) absl
  in
  absfree

/// Returns the list of free shadowed variables appearing in a term.
val shadowed_free_in : genv -> term -> Tac (list bv)
let shadowed_free_in ge t =
  let fvl = free_in t in
  List.Tot.filter (fun bv -> bv_is_shadowed ge bv) fvl

/// Returns true if a term contains variables which are shadowed in a given environment
val term_has_shadowed_variables : genv -> term -> Tac bool
let term_has_shadowed_variables ge t =
  let fvl = free_in t in
  Some? (List.Tot.tryFind (bv_is_shadowed ge) fvl)
