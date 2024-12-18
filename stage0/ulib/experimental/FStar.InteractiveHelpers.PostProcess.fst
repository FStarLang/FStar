module FStar.InteractiveHelpers.PostProcess

open FStar.List.Tot
open FStar.Tactics
open FStar.Mul
open FStar.InteractiveHelpers.Base
open FStar.InteractiveHelpers.ExploreTerm
open FStar.InteractiveHelpers.Propositions
open FStar.InteractiveHelpers.Effectful
open FStar.InteractiveHelpers.Output

/// The high-level post-processing tactics, used to retrieve some specific
/// information from the context and generate output which can be exploited
/// on the IDE side.

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(*** General utilities *)
/// We declare some identifiers that we will use to guide the meta processing
assume type meta_info
assume val focus_on_term : meta_info

let end_proof () =
  tadmit_t (`())

let unsquash_equality (t:term) : Tac (option (term & term)) =
  begin match term_as_formula t with
  | Comp (Eq _) l r -> Some (l, r)
  | _ -> None
  end

#push-options "--ifuel 2"
let pp_explore (dbg dfs : bool)
               (#a : Type0)
               (f : explorer a)
               (x : a) :
  Tac unit =
  let g = cur_goal () in
  let e = cur_env () in
  print_dbg dbg ("[> pp_explore:\n" ^ term_to_string g);
  begin match unsquash_equality g with
  | Some (l, _) ->
    let c = safe_typ_or_comp dbg e l in
    let ge = mk_genv e [] [] in
    print_dbg dbg ("[> About to explore term:\n" ^ term_to_string l);
    let x = explore_term dbg dfs #a f x ge [] c l in
    end_proof ()
  | _ -> mfail "pp_explore: not a squashed equality"
  end
#pop-options

/// This function goes through the goal, which is presumed to be a squashed equality,
/// and prints all the subterms of its left operand. Very useful for debugging.
val pp_explore_print_goal : unit -> Tac unit
let pp_explore_print_goal () =
  let f : explorer unit =
    fun _ _ _ _ _ -> ((), Continue)
  in
  pp_explore true false f ()

/// Check for meta-identifiers. Note that we can't simply use ``term_eq`` which
/// sometimes unexpectedly fails (maybe because of information hidden to Meta-F*)
val is_focus_on_term : term -> Tac bool
let is_focus_on_term t = is_fvar t (`%focus_on_term)

/// Check if a term is an assertion or an assumption and return its content
/// if it is the case.
val term_is_assert_or_assume : term -> Tac (option term)
let term_is_assert_or_assume t =
  match inspect t with
  | Tv_App hd (a, Q_Explicit) ->
    if is_any_fvar a [`%Prims._assert; `%FStar.Pervasives.assert_norm; `%Prims._assume]
    then Some a
    else None
  | _ -> None

/// Check if the given term view is of the form: 'let _ = focus_on_term in body'
/// Returns 'body' if it is the case.
val is_focused_term : term_view -> Tac (option term)
let is_focused_term tv =
  match tv with
  | Tv_Let recf attrs _ _ def body ->
    if is_focus_on_term def then Some body else None
  | _ -> None

noeq type exploration_result (a : Type)= {
  ge : genv;
  parents : list (genv & term_view);
  tgt_comp : option typ_or_comp;
  res : a;
}

let mk_exploration_result = Mkexploration_result

let pred_explorer (a:Type) = 
  genv -> list (genv & term_view) -> option typ_or_comp -> term_view ->
  Tac (option a)

val find_predicated_term_explorer : #a:Type0 -> pred_explorer a -> bool ->
                                    explorer (option (exploration_result a))
let find_predicated_term_explorer #a pred dbg acc ge pl opt_c t =
  if Some? acc then mfail "find_focused_term_explorer: non empty accumulator";
  if dbg then
    begin
    print ("[> find_focused_term_explorer: " ^ term_view_construct t ^ ":\n" ^ term_to_string t)
    end;
  match pred ge pl opt_c t with
  | Some ft -> Some (mk_exploration_result ge pl opt_c ft), Abort
  | None -> None, Continue

val find_predicated_term : #a:Type0 -> pred_explorer a -> bool -> bool ->
                           genv -> list (genv & term_view) ->
                           option typ_or_comp -> term ->
                           Tac (option (exploration_result a))
let find_predicated_term #a pred dbg dfs ge pl opt_c t =
  fst (explore_term dbg dfs #(option (exploration_result a))
                    (find_predicated_term_explorer #a pred dbg)
                    None ge pl opt_c t)

val _is_focused_term_explorer : pred_explorer term
let _is_focused_term_explorer ge pl opt_c tv =
  is_focused_term tv

val find_focused_term : bool -> bool -> genv -> list (genv & term_view) -> option typ_or_comp -> term ->
                        Tac (option (exploration_result term))
let find_focused_term dbg dfs ge pl opt_c t =
  find_predicated_term #term _is_focused_term_explorer dbg dfs ge pl opt_c t

/// This function raises a MetaAnalysis exception if it can't find a focused term
val find_focused_term_in_current_goal : bool -> Tac (exploration_result term)
let find_focused_term_in_current_goal dbg =
  let g = cur_goal () in
  let e = cur_env () in
  print_dbg dbg ("[> find_focused_assert_in_current_goal:\n" ^ term_to_string g);
  begin match unsquash_equality g with
  | Some (l, _) ->
    let c = safe_typ_or_comp dbg e l in
    let ge = mk_genv e [] [] in
    print_dbg dbg ("[> About to explore term:\n" ^ term_to_string l);
    begin match find_focused_term dbg true ge [] c l with
    | Some res ->
      print_dbg dbg ("[> Found focused term:\n" ^ term_to_string res.res);
      res
    | None ->
      mfail ("find_focused_term_in_current_goal: could not find a focused term in the current goal: "
             ^ term_to_string g)
    end
  | _ -> mfail "find_focused_term_in_current_goal: not a squashed equality"
  end

/// This function raises a MetaAnalysis exception if it can't find a focused term
val find_focused_assert_in_current_goal : bool -> Tac (exploration_result term)
let find_focused_assert_in_current_goal dbg =
  print_dbg dbg ("[> find_focused_assert_in_current_goal");
  let res = find_focused_term_in_current_goal dbg in
  print_dbg dbg ("[> Found focused term:\n" ^ term_to_string res.res);
  (* Check that it is an assert or an assume, retrieve the assertion *)
  let res' = 
    match inspect res.res with
    | Tv_Let _ _ bv0 ty fterm _ ->
      let ge' = genv_push_bv res.ge bv0 ty false None in
      ({ res with res = fterm; ge = ge' })
    | _ -> res
  in
  begin match term_is_assert_or_assume res'.res with
  | None -> mfail ("find_focused_assert_in_current_goal: the found focused term is not an assertion or an assumption:" ^ term_to_string res.res)
  | Some tm ->  { res' with res = tm }
  end

(*** Analyze effectful term *)
/// Analyze a term in order to print properly instantiated pre/postconditions
/// and type conditions.

/// with_globals states whether to analyze the target pre/post together with the
/// focused term.
val analyze_effectful_term : 
     dbg:bool
  -> with_gpre:bool
  -> with_gpost:bool
  -> res:exploration_result term
  -> Tac unit

let analyze_effectful_term dbg with_gpre with_gpost res =
  let ge = res.ge in
  let opt_c = res.tgt_comp in
  (* Analyze the effectful term and check whether it is a 'let' or not *)
  let ge1, studied_term, info, ret_bv, shadowed_bv, is_let =
    begin match inspect res.res with
    | Tv_Let _ _ bv0 ty fterm _ ->
      (* Before pushing the binder, check if it shadows another variable.
       * If it is the case, we will need it to correctly output the pre
       * and post-assertions (because for the pre-assertions the variable
       * will not be shadowed yet, while it will be the case for the post-
       * assertions) *)
      print_dbg dbg ("Restraining to: " ^ term_to_string fterm);
      let shadowed_bv : option bv =
        match genv_get_from_name ge (name_of_bv bv0) with
        | None -> None
        | Some (sbv, _) -> Some (fst sbv)
      in
      let ge1 = genv_push_bv ge bv0 ty false None in
      (* If the bv name is "uu___", introduce a fresh variable and use it instead:
       * the underscore might have been introduced when desugaring a let using
       * tuples. If doing that is not necessary, the introduced variable will
       * not appear in the generated assertions anyway. *)
      let ge2, (bv1 : bv) =
        let bvv0 = inspect_bv bv0 in
        let _ = print_dbg dbg ("Variable bound in let: " ^ abv_to_string bv0) in
        if unseal bvv0.bv_ppname = "uu___" (* this is a bit hacky *)
        then genv_push_fresh_bv ge1 "ret" ty
        else ge1, bv0
      in
      let info = compute_eterm_info dbg ge2.env fterm in
      (ge2, fterm, (info <: eterm_info), Some bv1, shadowed_bv, true)
    | _ -> (ge, res.res, compute_eterm_info dbg ge.env res.res, None, None, false)
    end
  in
  print_dbg dbg ("[> Focused term constructor: " ^ term_construct studied_term);
  print_dbg dbg ("[> Environment information (after effect analysis):\n" ^ genv_to_string ge1);
  (* Check if the considered term is an assert, in which case we will only
   * display the precondition (otherwise we introduce too many assertions
   * in the context) *)
  let is_assert = Some? (term_is_assert_or_assume studied_term) in
  (* Instantiate the refinements *)
  (* TODO: use bv rather than term for ret_arg *)
  let ret_arg = opt_tapply (fun x -> pack (Tv_Var x)) ret_bv in
  let parents = List.Tot.map snd res.parents in
  let ge2, asserts =
    eterm_info_to_assertions dbg with_gpre with_gpost ge1 studied_term is_let
                             is_assert info ret_arg opt_c parents [] in
  (* Simplify and filter *)
  let asserts = simp_filter_assertions ge2.env simpl_norm_steps asserts in
  (* Introduce fresh variables for the shadowed ones and substitute *)
  let ge3, asserts = subst_shadowed_with_abs_in_assertions dbg ge2 shadowed_bv asserts in
  (* If not a let, insert all the assertions before the term *)
  let asserts =
    if is_let then asserts
    else mk_assertions (List.Tot.append asserts.pres asserts.posts) []
  in
  (* Print *)
  printout_success ge3 asserts

[@plugin]
val pp_analyze_effectful_term : bool -> bool -> bool -> unit -> Tac unit
let pp_analyze_effectful_term dbg with_gpre with_gpost () =
  try
    let res = find_focused_term_in_current_goal dbg in
    analyze_effectful_term dbg with_gpre with_gpost res;
    end_proof ()
  with | MetaAnalysis msg -> printout_failure msg; end_proof ()
       | err -> (* Shouldn't happen, so transmit the exception for debugging *) raise err

(*** Split conjunctions *)
/// Split an assert made of conjunctions so that there is one assert per
/// conjunction. We try to be a bit smart. For instance, if the assertion is of
/// the form:
/// [> assert(let Construct x1 ... xn = e in A1 /\ ... /\ An);
/// We generate:
/// [> assert(let Construct x1 ... xn = e in A1);
/// [> ...
/// [> assert(let Construct x1 ... xn = e in An);

/// Remove ``b2t`` if it is the head of the term
val remove_b2t : term -> Tac term
let remove_b2t (t:term) : Tac term =
  match inspect t with
  | Tv_App hd (a, Q_Explicit) ->
    begin match inspect hd with
    | Tv_FVar fv ->
      if fv_eq_name fv b2t_qn then a else t
    | _ -> t
    end
  | _ -> t

// TODO: gather all the functions like split_conjunctions, is_eq...
/// Try to destruct a term of the form '_ && _' or '_ /\ _'
val is_conjunction : term -> Tac (option (term & term))
let is_conjunction t =
  let t = remove_b2t t in
  let hd, params = collect_app t in
  match params with
  | [(x,Q_Explicit);(y,Q_Explicit)] ->
    begin match inspect hd with
    | Tv_FVar fv ->
      let fvn = inspect_fv fv in
      if fvn = and_qn || fvn = ["Prims"; "op_AmpAmp"]
      then Some (x, y) else None
    | _ -> None
    end
  | _ -> None

val split_conjunctions : term -> Tac (list term)

let rec _split_conjunctions (ls : list term) (t : term) : Tac (list term) =
  match is_conjunction t with
  | None -> t :: ls
  | Some (l, r) ->
    let ls1 = _split_conjunctions ls r in
    let ls2 = _split_conjunctions ls1 l in
    ls2

let split_conjunctions t =
  _split_conjunctions [] t

/// Split a term of the form:
/// [> let Constuct x1 ... xn = x in A1 /\ ... /\ Am
/// into m terms:
/// [> let Constuct x1 ... xn = x in A1
/// ...
/// [> let Constuct x1 ... xn = x in Am
val split_conjunctions_under_match : bool -> term -> Tac (list term)

let split_conjunctions_under_match dbg t =
  let t1 = remove_b2t t in
  print_dbg dbg ("[> split_conjunctions_under_match: " ^ term_construct t1);
  match inspect t1 with
  | Tv_Match scrut ret_opt [(pat, br)] ->
    let tl = split_conjunctions br in
    map (fun x -> pack (Tv_Match scrut ret_opt [(pat, x)])) tl
  | _ ->
    (* Not of the proper shape: return the original term *)
    [t]

val split_assert_conjs : bool -> exploration_result term -> Tac unit
let split_assert_conjs dbg res =
  let ge0 = res.ge in
  (* Simplify the term (it may be an abstraction applied to some parameters) *)
  let t = norm_term_env ge0.env simpl_norm_steps res.res in
  (* Split the conjunctions *)
  let conjs = split_conjunctions t in
  (* If there is only one conjunction, check if it is of the following form
   * and try to split:
   * [> let Construct x1 .. xn = x in A1 /\ ... /\ Am
   *)
  let conjs =
    if List.Tot.length conjs = 1 then split_conjunctions_under_match dbg t
    else conjs
  in
  let asserts = mk_assertions conjs [] in
  (* Print *)
  printout_success ge0 asserts

[@plugin]
val pp_split_assert_conjs : bool -> unit -> Tac unit
let pp_split_assert_conjs dbg () =
  try
    let res = find_focused_assert_in_current_goal dbg in
    split_assert_conjs dbg res;
    end_proof ()
  with | MetaAnalysis msg -> printout_failure msg; end_proof ()
       | err -> (* Shouldn't happen, so transmit the exception for debugging *) raise err

(*** Term unfolding in assert *)
/// Unfold/rewrite a term in an assert.
/// If the term is a (recursive) top-level identifier, unfold it.
/// Otherwise look for an equality or a pure let-binding to replace it with.
/// If the assert is an equality, unfold/rewrite only on the side chosen by the user.

// TODO: use "kind" keyword rather than type above
/// An equality kind
noeq type eq_kind =
  | Eq_Dec    : typ -> eq_kind          (* =   *)
  | Eq_Undec  : typ -> eq_kind          (* ==  *)
  | Eq_Hetero : typ -> typ -> eq_kind   (* === *)

/// Deconstruct an equality
// We use our own construct because ``term_as_formula`` doesn't always work
// TODO: update ``term_as_formula``
val is_eq : bool -> term -> Tac (option (eq_kind & term & term))
let is_eq dbg t =
  let t = remove_b2t t in
  print_dbg dbg ("[> is_eq: " ^ term_to_string t);
  let hd, params = collect_app t in
  print_dbg dbg ("- hd:\n" ^ term_to_string hd);
  print_dbg dbg ("- parameters:\n" ^ list_to_string (fun (x, y) -> term_to_string x) params);
  match inspect hd with
  | Tv_FVar fv ->
    begin match params with
    | [(a,Q_Implicit);(x,Q_Explicit);(y,Q_Explicit)] ->
      if is_any_fvar a [`%Prims.op_Equality; `%Prims.equals; "Prims.op_Equals"] then
        Some ((Eq_Dec a), x, y)
      else if is_any_fvar a [`%Prims.eq2; "Prims.op_Equals_Equals"] then
        Some ((Eq_Undec a), x, y)
      else None
    | [(a,Q_Implicit);(b,Q_Implicit);(x,Q_Explicit);(y,Q_Explicit)] ->
      if is_fvar a (`%Prims.op_Equals_Equals_Equals) then
        Some ((Eq_Hetero a b), x, y)
      else None
    | _ -> None
    end
  | _ -> None

/// Reconstruct an equality
val mk_eq : eq_kind -> term -> term -> Tot term
let mk_eq k t1 t2 =
  match k with
  | Eq_Dec ty ->
    mk_app (`Prims.op_Equality) [(ty, Q_Implicit); (t1, Q_Explicit); (t2, Q_Explicit)]
  | Eq_Undec ty ->
    mk_app (`Prims.eq2) [(ty, Q_Implicit); (t1, Q_Explicit); (t2, Q_Explicit)]
  | Eq_Hetero ty1 ty2 ->
    mk_app Prims.(`( === )) [(ty1, Q_Implicit); (ty2, Q_Implicit);
                             (t1, Q_Explicit); (t2, Q_Explicit)]

let formula_construct (f : formula) : Tac string =
  match f with
  | True_       -> "True_"
  | False_      -> "False_"
  | Comp _ _ _  -> "Comp"
  | And _ _     -> "And"
  | Or _ _      -> "Or"
  | Not _       -> "Not"
  | Implies _ _ -> "Implies"
  | Iff _ _     -> "Iff"
  | Forall _ _ _ -> "Forall"
  | Exists _ _ _ -> "Exists"
  | App _ _     -> "Apply"
  | Name _      -> "Name"
  | FV _        -> "FV"
  | IntLit _    -> "IntLit"
  | F_Unknown   -> "F_Unknown"

/// Check if a proposition is an equality which can be used to rewrite a term.
/// Return the operand of the equality which the term is equal to if it is the case.
val is_equality_for_term : bool -> term -> term -> Tac (option term)
let is_equality_for_term dbg tm p =
  print_dbg dbg ("[> is_equality_for_term:" ^
                 "\n- term: " ^ term_to_string tm ^
                 "\n- prop: " ^ term_to_string p);
  (* Specialize equality for bv - TODO: not sure if necessary, but I had problems
   * in the past *)
  let check_eq : term -> Tac bool =
    match inspect tm with
    | Tv_Var bv ->
      (fun tm' -> match inspect tm' with | Tv_Var bv' -> bv_eq bv bv' | _ -> false)
    | _ -> (fun tm' -> term_eq tm tm')
  in    
  match is_eq dbg p with
  | Some (ekind, l, r) ->
    (* We ignore heterogeneous equality, because it risks to cause havoc at
     * typing after substitution *)
    print_dbg dbg ("Term is eq: " ^ term_to_string l ^ " = " ^ term_to_string r);
    if Eq_Hetero? ekind then
      begin
      print_dbg dbg "Ignoring heterogeneous equality";
      None
      end
    else if check_eq l then Some r
    else if check_eq r then Some l
    else None
  | _ ->
    print_dbg dbg "Term is not eq";
    None

val find_subequality : bool -> term -> term -> Tac (option term)
let find_subequality dbg tm p =
  print_dbg dbg ("[> find_subequality:" ^ 
                 "\n- ter  : " ^ term_to_string tm ^
                 "\n- props: " ^ term_to_string p);
  let conjuncts = split_conjunctions p in
  print_dbg dbg ("Conjuncts:\n" ^ list_to_string term_to_string conjuncts);
  tryPick (is_equality_for_term dbg tm) conjuncts

/// Look for an equality in a postcondition which can be used for rewriting.
val find_equality_from_post :
  bool -> genv -> term -> bv -> typ -> term -> effect_info ->
  list term_view -> list term_view -> Tac (genv & option term)
let find_equality_from_post dbg ge0 tm let_bv let_bvty ret_value einfo parents children =
  print_dbg dbg "[> find_equality_from_post";
  let tinfo = get_type_info_from_type let_bvty in
  (* Compute the post-condition *)
  let ge1, _, post_prop =
    pre_post_to_propositions dbg ge0 einfo.ei_type ret_value (Some (mk_binder let_bv let_bvty))
                             tinfo einfo.ei_pre einfo.ei_post parents children
  in
  print_dbg dbg ("Computed post: " ^ option_to_string term_to_string post_prop);
  (* Look for an equality in the post *)
  let res =
    match post_prop with
    | None -> None
    | Some p -> find_subequality dbg tm p
  in
  (* If we found something, we return the updated environment,
   * otherwise we can return the original one *)
  match res with
  | None -> ge0, None
  | Some tm -> ge1, Some tm

/// Given a list of parent terms (as generated by ``explore_term``), look for an
/// equality given by a post-condition which can be used to replace a term.
val find_context_equality :
     dbg:bool
  -> ge0:genv
  -> tm:term
  -> parents:list term_view
  -> children:list term_view
  -> Tac (genv & option term)

/// Auxiliary function which actually performs the search
let rec find_context_equality_aux dbg ge0 tm (opt_bv : option bv)
                                  (parents children : list term_view) :
  Tac (genv & option term) =
  match parents with
  | [] -> ge0, None
  | tv :: parents' ->
    print_dbg dbg ("[> find_context_equality:\n" ^
                   "- term  : " ^ term_to_string tm ^ "\n" ^
                   "- parent: " ^ term_to_string tv);
    (* We only consider let-bindings *)
    match tv with
    | Tv_Let _ _ bv' ty def _ ->
      print_dbg dbg "Is Tv_Let";
      let tm_info = compute_eterm_info dbg ge0.env def in
      let einfo = tm_info.einfo in
      (* If the searched term is a bv and the current let is the one which
       * introduces it:
       * - if the term is effectful, use it
       * - otherwise, try to use its postcondition. If we don't find any
       *   equalities, some there *)
      let let_bv_is_tm =
        match opt_bv with
        | Some tm_bv -> bv_eq tm_bv bv'
        | None -> false
      in
      if let_bv_is_tm && effect_type_is_pure einfo.ei_type then ge0, Some def
      else
        let ret_value = pack (Tv_Var bv') in
        begin match find_equality_from_post dbg ge0 tm bv' ty ret_value
                                            einfo parents children with
        | ge1, Some p -> ge1, Some p
        | _, None -> find_context_equality_aux dbg ge0 tm opt_bv parents' (tv :: children)
        end
   | _ -> find_context_equality_aux dbg ge0 tm opt_bv parents' (tv :: children)

let find_context_equality dbg ge0 tm parents children =
  let opt_bv =
    match inspect tm with
    | Tv_Var bv -> Some bv
    | _ -> None
  in
  find_context_equality_aux dbg ge0 tm opt_bv parents children

/// Replace a subterm by another term
val replace_term_in : bool -> term -> term -> term -> Tac term
let rec replace_term_in dbg from_term to_term tm =
  if term_eq from_term tm then to_term else
  match inspect tm with
  | Tv_Var _ | Tv_BVar _ | Tv_FVar _ -> tm
  | Tv_App hd (a, qual) ->
    let a' = replace_term_in dbg from_term to_term a in
    let hd' = replace_term_in dbg from_term to_term hd in
    pack (Tv_App hd' (a', qual))
  | Tv_Abs br body ->
    let body' = replace_term_in dbg from_term to_term body in
    pack (Tv_Abs br body')
  | Tv_Arrow br c0 -> tm (* TODO: we might want to explore that *)
  | Tv_Type _ -> tm
  | Tv_Refine bv sort ref ->
    let sort' = replace_term_in dbg from_term to_term sort in
    let ref' = replace_term_in dbg from_term to_term ref in
    pack (Tv_Refine bv sort' ref')
  | Tv_Const _ -> tm
  | Tv_Uvar _ _ -> tm
  | Tv_Let recf attrs bv ty def body ->
    (* GM 2023-04-27: leaving ty untouched, old code did not
       descend into sort. *)
    let def' = replace_term_in dbg from_term to_term def in
    let body' = replace_term_in dbg from_term to_term body in
    pack (Tv_Let recf attrs bv ty def' body')
  | Tv_Match scrutinee ret_opt branches ->  //AR: TODO: account for the returns annotation
    (* Auxiliary function to explore the branches *)
    let explore_branch (br : branch) : Tac branch =
      (* Only explore the branch body *)
      let pat, body = br in
      let body' = replace_term_in dbg from_term to_term body in
      (pat, body')
    in
    let scrutinee' = replace_term_in dbg from_term to_term scrutinee in
    let branches' = map explore_branch branches in
    pack (Tv_Match scrutinee' ret_opt branches')
  | Tv_AscribedT e ty tac use_eq ->
    let e' = replace_term_in dbg from_term to_term e in
    let ty' = replace_term_in dbg from_term to_term ty in
    pack (Tv_AscribedT e' ty' tac use_eq)
  | Tv_AscribedC e c tac use_eq ->
    let e' = replace_term_in dbg from_term to_term e in
    pack (Tv_AscribedC e' c tac use_eq)
  | _ ->
    (* Unknown *)
    tm

val strip_implicit_parameters : term -> Tac term
let rec strip_implicit_parameters tm =
  match inspect tm with
  | Tv_App hd (a,qualif) ->
    if Q_Implicit? qualif then strip_implicit_parameters hd else tm
  | _ -> tm

val unfold_in_assert_or_assume : bool -> exploration_result term -> Tac unit
let unfold_in_assert_or_assume dbg ares =
  print_dbg dbg ("[> unfold_in_assert_or_assume:\n" ^ term_to_string ares.res);
  (* Find the focused term inside the assert, and on which side of the
   * equality if the assert is an equality *)
  let find_focused_in_term t =
    find_focused_term dbg false ares.ge ares.parents ares.tgt_comp t
  in
  let find_in_whole_term () : Tac _ =
    match find_focused_in_term ares.res with
    | Some res ->
      ares.res, res, (fun x -> x <: Tac term), true
    | None -> mfail "unfold_in_assert_or_assume: could not find a focused term in the assert"
  in
  (* - subterm: the subterm of the assertion in which we found the focused term
   *   (if an equality, left or right operand, otherwise whole assertion)
   * - unf_res: the result of the exploration for the focused term inside the
   *   assertion, which gives the term to unfold
   * - rebuild: a Tot function which, given a term, rebuilds the equality by
   *   replacing the above subterm with the given term
   * - insert_before: whether to insert the new assertion before or after the
   *   current assertion in the user file *)
  let subterm, unf_res, (rebuild : term -> Tac term), insert_before =
    let _ = print_dbg dbg ("Assertion: " ^ term_to_string ares.res) in
    match is_eq dbg ares.res with
    | Some (kd, l, r) ->
      print_dbg dbg "The assertion is an equality";
      begin match find_focused_in_term l with
      | Some res ->
        print_dbg dbg ("Found focused term in left operand:" ^
                       "\n- left   : " ^ term_to_string l ^
                       "\n- right  : " ^ term_to_string r ^
                       "\n- focused: " ^ term_to_string res.res);
        let rebuild t : Tac term = mk_eq kd t r in
        l, res, rebuild, true
      | None ->
        begin match find_focused_in_term r with
        | Some res ->
          print_dbg dbg ("Found focused term in right operand:" ^
                 "\n- left   : " ^ term_to_string l ^
                 "\n- right  : " ^ term_to_string r ^
                 "\n- focused: " ^ term_to_string res.res);
          let rebuild (t : term) : Tac term = mk_eq kd l t in
          r, res, rebuild, false
        | None ->
          mfail "unfold_in_assert_or_assume: could not find a focused term in the assert"
        end
      end
    | None -> 
      print_dbg dbg "The assertion is not an equality";
      find_in_whole_term ()
  in
  print_dbg dbg ("Found subterm in assertion/assumption:\n" ^
                 "- subterm: " ^ term_to_string subterm ^ "\n" ^
                 "- focused term: " ^ term_to_string unf_res.res);
  (* Unfold the term *)
  let res_view = inspect unf_res.res in
  let ge1, opt_unf_tm =
    match res_view with
    | Tv_FVar fv ->
      print_dbg dbg ("The focused term is a top identifier: " ^ fv_to_string fv);
      (* The easy case: just use the normalizer *)
      let fname = flatten_name (inspect_fv fv) in
      let subterm' = norm_term_env ares.ge.env [delta_only [fname]; zeta] subterm in
      print_dbg dbg ("Normalized subterm: " ^ term_to_string subterm');
      ares.ge, Some subterm'
    | _ ->
      (* Look for an equality given by a previous post-condition. In the case
       * the term is a bv, we can also use the let-binding which introduces it,
       * if it is pure. *)
      let parents = List.Tot.map snd ares.parents in
      let opt_bvty : option (bv & typ) =
        match res_view with
        | Tv_Var bv ->
          print_dbg dbg ("The focused term is a local variable: " ^ bv_to_string bv);
          (* Check that the binder was not introduced by an abstraction inside the assertion *)
          if not (Some? (genv_get ares.ge bv)) then
            mfail "unfold_in_assert_or_assume: can't unfold a variable locally introduced in an assertion";
          Some (bv, pack_ln Tv_Unknown) // FIXME
        | _ ->
          print_dbg dbg ("The focused term is an arbitrary term: " ^ term_to_string unf_res.res);
          None
      in
      let ge1, eq_tm = find_context_equality dbg ares.ge unf_res.res parents [] in
      (* Check if we found an equality *)
      let opt_eq_tm =
        match eq_tm with
        | Some eq_tm -> Some eq_tm
        | _ -> None
      in
      (* Apply it *)
      let subterm' =
        match opt_bvty, opt_eq_tm with
        | Some bvty, Some eq_tm -> Some (apply_subst ge1.env subterm [(bvty, eq_tm)])
        | None, Some eq_tm -> Some (replace_term_in dbg unf_res.res eq_tm subterm)
        | _ -> None
      in
      ge1, subterm'
  in
  (* If we couldn't unfold the term, check if it is a top-level identifier with
   * implicit parameters (it may happen that the user calls the command on a
   * top-level identifier which has implicit parameters without providing
   * those parameters, in which case the focused term is the identifier applied
   * to those implicits inferred by F*, and thus an app and not an fvar).
   * Note that so far we have no way to check if the implicit parameters have
   * been explicitly provided by the user or not, which is why we can't do better
   * than greedy tests.*)
  let ge2, unf_tm =
    match opt_unf_tm with
    | Some unf_tm -> ge1, unf_tm
    | None ->
      begin match inspect (strip_implicit_parameters unf_res.res) with
      | Tv_FVar fv ->
        print_dbg dbg ("The focused term is a top identifier with implicit parameters: "
                       ^ fv_to_string fv);
        (* The easy case: just use the normalizer *)
        let fname = flatten_name (inspect_fv fv) in
        let subterm' = norm_term_env ge1.env [delta_only [fname]; zeta] subterm in
        print_dbg dbg ("Normalized subterm: " ^ term_to_string subterm');
        ge1, subterm'
      | _ ->        
        mfail ("unfold_in_assert_or_assume: " ^
               "couldn't find equalities with which to rewrite: " ^
               term_to_string unf_res.res)
      end
  in
  (* Create the assertions to output *)
  let final_assert = rebuild unf_tm in
  let final_assert = prettify_term dbg final_assert in
  print_dbg dbg ("-> Final assertion:\n" ^ term_to_string final_assert);
  let asserts =
    if insert_before then mk_assertions [final_assert] [] else mk_assertions [] [final_assert]
  in
  (* Introduce fresh variables for the shadowed ones and substitute *)
  let ge3, asserts = subst_shadowed_with_abs_in_assertions dbg ge2 None asserts in
  (* Output *)
  printout_success ge3 asserts

[@plugin]
val pp_unfold_in_assert_or_assume : bool -> unit -> Tac unit
let pp_unfold_in_assert_or_assume dbg () =
  try
    let res = find_focused_assert_in_current_goal dbg in
    unfold_in_assert_or_assume dbg res;
    end_proof ()
  with | MetaAnalysis msg -> printout_failure msg; end_proof ()
       | err -> (* Shouldn't happen, so transmit the exception for debugging *) raise err
