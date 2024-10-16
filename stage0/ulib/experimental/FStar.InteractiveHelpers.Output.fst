module FStar.InteractiveHelpers.Output

open FStar.List.Tot
open FStar.Tactics
open FStar.Mul
open FStar.InteractiveHelpers.Base
open FStar.InteractiveHelpers.ExploreTerm
open FStar.InteractiveHelpers.Propositions

/// Facilities to output results to the IDE/emacs/whatever.
/// Contains datatypes and functions to carry information.

#set-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(*** Convert terms to string *)
/// The important point is to handle variable shadowing properly, so that the
/// generated term is meaningful in the user context, or at least that it is clear
/// to the user that some variables are shadowed.

/// Introduce fresh variables for the variables shadowed in the current environment
/// and substitute them in the terms. Note that as the binding of the value returned
/// by a function application might shadow one of its parameters, we need to treat
/// differently the pre-assertions and the post-assertions. Moreover, we need to
/// keep track of which variables are shadowed for every assertion.
  
let rec _split_subst_at_bv (#a #b : Type) (x : bv) (subst : list ((bv & a) & b)) :
  Tot (list ((bv & a) & b) & list ((bv & a) & b))
  (decreases subst) =
  match subst with
  | [] -> [], []
  | ((src, ty), tgt) :: subst' ->
    if bv_eq x src then
      [], subst'
    else 
      let s1, s2 = _split_subst_at_bv x subst' in
      ((src, ty), tgt) :: s1, s2

val subst_shadowed_with_abs_in_assertions : bool -> genv -> option bv -> assertions -> Tac (genv & assertions)
let subst_shadowed_with_abs_in_assertions dbg ge shadowed_bv es =
  (* When generating the substitution, we need to pay attention to the fact that
   * the returned value potentially bound by a let may shadow another variable.
   * We need to take this into account for the post-assertions (but not the
   * pre-assertions). *)
  print_dbg dbg ("subst_shadowed_with_abs_in_assertions:\n" ^ genv_to_string ge);
  (* Generate the substitution *)
  let ge1, subst = generate_shadowed_subst ge in
  let post_subst = map (fun (src, ty, tgt) -> (src, ty), pack (Tv_Var tgt)) subst in
  (* The current substitution is valid for the post-assertions: derive from it
   * a substitution valid for the pre-assertions (just cut it where the bv
   * shadowed by the return value appears). Note that because we might introduce
   * dummy variables for the return value, it is not valid just to ignore
   * the last substitution pair. *)
  let pre_subst =
    if Some? shadowed_bv then fst (_split_subst_at_bv (Some?.v shadowed_bv) post_subst)
    else post_subst
  in
  let subst_to_string subst : Tac string =
    let to_string ((x, ty), y) =
      "(" ^ abv_to_string x ^ " -> " ^ term_to_string y ^ ")\n"
    in
    let str = map to_string subst in
    List.Tot.fold_left (fun x y -> x ^ y) "" str
  in
  if dbg then
    begin
    print_dbg dbg ("- pre_subst:\n" ^ subst_to_string pre_subst);
    print_dbg dbg ("- post_subst:\n" ^ subst_to_string post_subst)
    end;
  (* Apply *)
  let apply = (fun s -> map (fun t -> apply_subst ge1.env t s)) in
  let pres = apply pre_subst es.pres in
  let posts = apply post_subst es.posts in
  ge1, mk_assertions pres posts

(*** Convert propositions to string *)
/// Originally: we output the ``eterm_info`` and let the emacs commands do some
/// filtering and formatting. Now, we convert ``eterm_info`` to a ``assertions``.
/// Note that we also convert all the information to a string that we export at
/// once in order for the output not to be polluted by any other messages
/// (warning messages from F*, for example).

let string_to_printout (prefix data:string) : Tot string =
  prefix ^ ":\n" ^ data ^ "\n"

let term_to_printout (ge:genv) (prefix:string) (t:term) : Tac string =
  (* We need to look for abstract variables and abstract them away *)
  let abs = abs_free_in ge t in
  let abs_binders = List.Tot.map (fun (bv, t) -> mk_binder bv t) abs in
  let abs_terms = map (fun (bv, _) -> pack (Tv_Var bv)) abs in
  let t = mk_abs abs_binders t in
  let t = mk_e_app t abs_terms in
  string_to_printout prefix (term_to_string t)

let opt_term_to_printout (ge:genv) (prefix:string) (t:option term) : Tac string =
  match t with
  | Some t' -> term_to_printout ge prefix t'
  | None -> string_to_printout prefix ""

let proposition_to_printout (ge:genv) (prefix:string) (p:proposition) : Tac string =
  term_to_printout ge prefix p

let propositions_to_printout (ge:genv) (prefix:string) (pl:list proposition) : Tac string =
  let prop_to_printout i p =
    let prefix' = prefix ^ ":prop" ^ string_of_int i in
    proposition_to_printout ge prefix' p
  in
  let str = string_to_printout (prefix ^ ":num") (string_of_int (List.Tot.length pl)) in
  let concat_prop s_i p : Tac (string & int) =
    let s, i = s_i in
    s ^ prop_to_printout i p, i+1
  in
  let str, _ = fold_left concat_prop (str,0) pl in
  str

let error_message_to_printout (prefix : string) (message : option string) : Tot string =
  let msg = match message with | Some msg -> msg | _ -> "" in
  string_to_printout (prefix ^ ":error") msg

/// Utility type and function to communicate the results to emacs.
noeq type export_result =
| ESuccess : ge:genv -> a:assertions -> export_result
| EFailure : err:string -> export_result

let result_to_printout (prefix:string) (res:export_result) :
  Tac string =
  let str = prefix ^ ":BEGIN\n" in
  (* Note that the emacs commands will always look for fields for the error message
   * and the pre/post assertions, so we need to generate them, even though they
   * might be empty. *)
  let err, ge, pres, posts =
    match res with
    | ESuccess ge a -> None, ge, a.pres, a.posts
    | EFailure err ->
      let ge = mk_init_genv (top_env ()) in (* dummy environment - will not be used *)
      Some err, ge, [], []
  in
  (* Error message *)
  let str = str ^ error_message_to_printout prefix err in
  (* Assertions *)
  let str = str ^ propositions_to_printout ge (prefix ^ ":pres") pres in
  let str = str ^ propositions_to_printout ge (prefix ^ ":posts") posts in
  str ^ prefix ^ ":END\n" ^ "%FIH:FSTAR_META:END%"

let printout_result (prefix:string) (res:export_result) :
  Tac unit =
  print (result_to_printout prefix res)

/// The function to use to export the results in case of success
let printout_success (ge:genv) (a:assertions) : Tac unit =
  printout_result "ainfo" (ESuccess ge a)

/// The function to use to communicate failure in case of error
let printout_failure (err : error_message) : Tac unit =
  printout_result "ainfo" (EFailure (rendermsg err))

let _debug_print_var (name : string) (t : term) : Tac unit =
  print ("_debug_print_var: " ^ name ^ ": " ^ term_to_string t);
  begin match safe_tc (top_env ()) t with
  | Some ty -> print ("type: " ^ term_to_string ty)
  | _ -> ()
  end;
  print ("qualifier: " ^ term_construct t);
  begin match inspect t with
  | Tv_Var bv ->
    let b : bv_view = inspect_bv bv in
    print ("Tv_Var: ppname: " ^ name_of_bv bv ^
           "; index: " ^ (string_of_int b.bv_index))
  | _ -> ()
  end;
  print "end of _debug_print_var"

/// We use the following to solve goals requiring a unification variable (for
/// which we might not have a candidate, or for which the candidate may not
/// typecheck correctly). We can't use the tactic ``tadmit`` for the simple
/// reason that it generates a warning which may mess up with the subsequent
/// parsing of the data generated by the tactics.
// TODO: actually, there already exists Prims.magic
assume val magic_witness (#a : Type) : a

let tadmit_no_warning () : Tac unit =
  apply (`magic_witness)

let pp_tac () : Tac unit =
  print ("post-processing: " ^ (term_to_string (cur_goal ())));
  dump "";
  trefl()

