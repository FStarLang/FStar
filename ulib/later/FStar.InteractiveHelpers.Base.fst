module FStar.InteractiveHelpers.Base

open FStar.List
open FStar.Tactics
open FStar.Mul

let var = namedv
let var_to_string = namedv_to_string
let inspect_var = inspect_namedv
let var_eq v1 v2 = (inspect_namedv v1).uniq = (inspect_namedv v2).uniq
let compare_var = compare_namedv

#push-options "--z3rlimit 15 --fuel 0 --ifuel 1"

(*** Utilities *)

val fv_eq : fv -> fv -> Tot bool
let fv_eq fv1 fv2 =
  let n1 = inspect_fv fv1 in
  let n2 = inspect_fv fv2 in
  n1 = n2

// TODO: use everywhere
val fv_eq_name : fv -> name -> Tot bool
let fv_eq_name fv n =
  let fvn = inspect_fv fv in
  fvn = n

// TODO: use more
val opt_apply (#a #b : Type) (f : a -> Tot b) (x : option a) : Tot (option b)
let opt_apply #a #b f x =
  match x with
  | None -> None
  | Some x' -> Some (f x')

val opt_tapply (#a #b : Type) (f : a -> Tac b) (x : option a) : Tac (option b)
let opt_tapply #a #b f x =
  match x with
  | None -> None
  | Some x' -> Some (f x')

val option_to_string : (#a : Type) -> (a -> Tac string) -> option a -> Tac string
let option_to_string #a f x =
  match x with
  | None -> "None"
  | Some x' -> "Some (" ^ f x' ^ ")"


let opt_cons (#a : Type) (opt_x : option a) (ls : list a) : Tot (list a) =
  match opt_x with
  | Some x -> x :: ls
  | None -> ls

val list_to_string : #a : Type -> (a -> Tac string) -> list a -> Tac string
let list_to_string #a f ls =
  (Tactics.Util.fold_left (fun s x -> s ^ " (" ^ f x ^ ");") "[" ls) ^ "]"


/// Apply a term to a list of parameters, normalize the result to make sure
/// all the abstractions are simplified
val mk_app_norm : env -> term -> list term -> Tac term
let mk_app_norm e t params =
  let t1 = mk_e_app t params in
  let t2 = norm_term_env e [] t1 in
  t2

val opt_mk_app_norm : env -> option term -> list term -> Tac (option term)
let opt_mk_app_norm e opt_t params =
  opt_tapply (fun t -> mk_app_norm e t params) opt_t

// TODO: remove
let rec unzip #a #b (l : list (a & b)) : Tot (list a & list b) =
  match l with
  | [] -> ([],[])
  | (hd1,hd2)::tl ->
       let (tl1,tl2) = unzip tl in
       (hd1::tl1,hd2::tl2)

/// Alternative ``namedv_to_string`` function where we print the index of the namedv.
/// It can be very useful for debugging.
let abv_to_string (v:var) : Tac string =
  let vv = inspect_var v in
  unseal vv.ppname ^ " (%" ^ string_of_int vv.uniq ^ ")"

let print_binder_info (full : bool) (b : binding) : Tac unit =
  if full then
    print (
      "> print_binder_info:" ^
      "\n- name: " ^ unseal b.ppname ^
      "\n- as string: " ^ binding_to_string b ^
      "\n- sort: " ^ term_to_string b.sort
    )
  else print (binding_to_string b)

let print_binders_info (full : bool) (e:env) : Tac unit =
  iter (print_binder_info full) (vars_of_env e)

let acomp_to_string (c:comp) : Tac string =
  match inspect_comp c with
  | C_Total ret ->
    "C_Total (" ^ term_to_string ret ^ ")"
  | C_GTotal ret ->
    "C_GTotal (" ^ term_to_string ret ^ ")"
  | C_Lemma pre post patterns ->
    "C_Lemma (" ^ term_to_string pre ^ ") (" ^ term_to_string post ^ ")"
  | C_Eff us eff_name result eff_args _ ->
    let eff_arg_to_string (a : term) : Tac string =
      " (" ^ term_to_string a ^ ")"
    in
    let args_str = map (fun (x, y) -> eff_arg_to_string x) eff_args in
    let args_str = List.Tot.fold_left (fun x y -> x ^ y) "" args_str in
    "C_Eff (" ^ flatten_name eff_name ^ ") (" ^ term_to_string result ^ ")" ^ args_str

exception MetaAnalysis of string
let mfail str =
  raise (MetaAnalysis str)

(*** Debugging *)
/// Some debugging facilities
val print_dbg : bool -> string -> Tac unit
let print_dbg debug s =
  if debug then print s

/// Return the qualifier of a term as a string
val term_view_construct (t : term_view) : Tac string

let term_view_construct (t : term_view) : Tac string =
  match t with
  | Tv_Var _ -> "Tv_Var"
  | Tv_BVar _ -> "Tv_BVar"
  | Tv_FVar _ -> "Tv_FVar"
  | Tv_App _ _ -> "Tv_App"
  | Tv_Abs _ _ -> "Tv_Abs"
  | Tv_Arrow _ _ -> "Tv_Arrow"
  | Tv_Type _ -> "Tv_Type"
  | Tv_Refine _ _ -> "Tv_Refine"
  | Tv_Const _ -> "Tv_Const"
  | Tv_Uvar _ _ -> "Tv_Uvar"
  | Tv_Let _ _ _ _ _ -> "Tv_Let"
  | Tv_Match _ _ _ -> "Tv_Match"
  | Tv_AscribedT _ _ _ _ -> "Tv_AscribedT"
  | Tv_AscribedC _ _ _ _ -> "Tv_AScribedC"
  | _ -> "Tv_Unknown"

val term_construct (t : term) : Tac string

let term_construct (t : term) : Tac string =
  term_view_construct (inspect t)

(*** Pretty printing *)
/// There are many issues linked to terms (pretty) printing.
/// The first issue is that when parsing terms, F* automatically inserts
/// ascriptions, which then clutter the terms printed to the user. The current
/// workaround is to filter those ascriptions in the terms before exploiting them.
/// TODO: this actually doesn't work for some unknown reason: some terms like [a /\ b]
/// become [l_and a b]...

val filter_ascriptions : bool -> term -> Tac term

let filter_ascriptions dbg t =
  print_dbg dbg ("[> filter_ascriptions: " ^ term_construct t ^ ": " ^ term_to_string t );
  visit_tm (fun t ->
    match inspect t with
    | Tv_AscribedT e _ _ _
    | Tv_AscribedC e _ _ _ -> e
    | _ -> t) t

/// Our prettification function. Apply it to all the terms which might be printed
/// back to the user. Note that the time at which the function is applied is
/// important: we can't apply it on all the assertions we export to the user, just
/// before exporting, because we may have inserted ascriptions on purpose, which
/// would then be filtered away.
val prettify_term : bool -> term -> Tac term
let prettify_term dbg t = filter_ascriptions dbg t

(*** Environments *)
/// We need a way to handle environments with variable bindings
/// and name shadowing, to properly display the context to the user.

/// A map linking variables to terms. For now we use a list to define it, because
/// there shouldn't be too many bindings.
type bind_map (a : Type) = list (var & a)

let bind_map_push (#a:Type) (m:bind_map a) (v:var) (x:a) = (v,x)::m

let rec bind_map_get (#a:Type) (m:bind_map a) (v:var) : Tot (option a) =
  match m with
  | [] -> None
  | (v', x)::m' ->
    if compare_var v v' = Order.Eq then Some x else bind_map_get m' v

let rec bind_map_get_from_name (#a:Type) (m:bind_map a) (name:string) :
  Tac (option (var & a)) =
  match m with
  | [] -> None
  | (v', x)::m' ->
    let v'v = inspect_var v' in
    if unseal v'v.ppname = name then Some (v', x) else bind_map_get_from_name m' name

noeq type genv =
{
  env : env;
  (* Whenever we evaluate a let binding, we keep track of the relation between
   * the binder and its definition.
   * The boolean indicates whether or not the variable is considered abstract. We
   * often need to introduce variables which don't appear in the user context, for
   * example when we need to deal with a postcondition for Stack or ST, which handles
   * the previous and new memory states, and which may not be available in the user
   * context, or where we don't always know which variable to use.
   * In this case, whenever we output the term, we write its content as an
   * abstraction applied to those missing parameters. For instance, in the
   * case of the assertion introduced for a post-condition:
   * [> assert((fun h1 h2 -> post) h1 h2);
   * Besides the informative goal, the user can replace those parameters (h1
   * and h2 above) by the proper ones then normalize the assertion by using
   * the appropriate command to get a valid assertion. *)
  bmap : bind_map (typ & bool & term);
  (* Whenever we introduce a new variable, we check whether it shadows another
   * variable because it has the same name, and put it in the below
   * list. Of course, for the F* internals such shadowing is not an issue, because
   * the index of every variable should be different, but this is very important
   * when generating code for the user *)
  svars : list (var & typ);
}

let get_env (e:genv) : env = e.env
let get_bind_map (e:genv) : bind_map (typ & bool & term) = e.bmap
let mk_genv env bmap svars : genv = Mkgenv env bmap svars
let mk_init_genv env : genv = mk_genv env [] []

val genv_to_string : genv -> Tac string
let genv_to_string ge =
  let binders_str = map binding_to_string (vars_of_env ge.env) in
  let bmap_elem_to_string (e : var & (typ & bool & term)) : Tac string =
    let v, (_sort, abs, t) = e in
    "(" ^ abv_to_string v ^" -> (" ^
    string_of_bool abs ^ ", " ^ term_to_string t ^ "))\n"
  in
  let bmap_str = map bmap_elem_to_string ge.bmap in
  let svars_str = map (fun (v, _) -> abv_to_string v ^ "\n") ge.svars in
  let flatten = List.Tot.fold_left (fun x y -> x ^ y) "" in
  "> env:\n" ^ flatten binders_str ^
  "> bmap:\n" ^ flatten bmap_str ^
  "> svars:\n" ^ flatten svars_str

let genv_get (ge:genv) (v:var) : Tot (option (typ & bool & term)) =
  bind_map_get ge.bmap v

let genv_get_from_name (ge:genv) (name:string) : Tac (option ((var & typ) & (bool & term))) =
  (* tweak return a bit to include sort *)
  match bind_map_get_from_name ge.bmap name with
  | None -> None
  | Some (v, (sort, b, x)) -> Some ((v, sort), (b, x))

(* TODO: MOVE *)
let namedv_to_binding (v:var) (sort : typ) : binding =
  let vv = inspect_var v in
  {
    ppname = vv.ppname;
    uniq   = vv.uniq;
    sort   = sort;
  }

/// Push a binder to a ``genv``. Optionally takes a ``term`` which provides the
/// term the binder is bound to (in a `let _ = _ in` construct for example).
let genv_push_binding (ge:genv) (b:binding) (abs:bool) (t:option term) : Tac genv =
  let sv = genv_get_from_name ge (unseal b.ppname) in
  let svars' = if Some? sv then fst (Some?.v sv) :: ge.svars else ge.svars in
  let e' = push_binding ge.env b in
  let v = binding_to_namedv b in
  let tm = if Some? t then Some?.v t else pack (Tv_Var v) in
  let bmap' = bind_map_push ge.bmap v (b.sort, abs, tm) in
  mk_genv e' bmap' svars'

/// Check if a binder is shadowed by another more recent binder
let var_is_shadowed (ge : genv) (v : var) : Tot bool =
  List.Tot.existsb (fun (v',_) -> var_eq v v') ge.svars

let binding_is_shadowed (ge : genv) (b : binding) : Tot bool =
  var_is_shadowed ge (binding_to_namedv b)

val var_is_abstract : genv -> var -> Tot bool
let var_is_abstract ge var =
  match genv_get ge var with
  | None -> false
  | Some (_, abs, _) -> abs

val binder_is_abstract : genv -> binding -> Tot bool
let binder_is_abstract ge v = var_is_abstract ge (binding_to_namedv v)

val genv_abstract_vars : genv -> Tot (list (var & typ))
let genv_abstract_vars ge =
  List.Tot.concatMap
    (fun (v, (ty, abs, _)) -> if abs then [v,ty] else []) ge.bmap

/// Versions of ``fresh_bv`` and ``fresh_binder`` inspired by the standard library
/// We make sure the name is fresh because we need to be able to generate valid code
/// (it is thus not enough to have a fresh integer).
let rec _fresh_name binder_names basename i : Tac string =
  let name = basename ^ string_of_int i in
  (* In worst case the performance is quadratic in the number of binders.
   * TODO: fix that, it actually probably happens for anonymous variables ('_') *)
  if List.mem name binder_names
  then _fresh_name binder_names basename (i+1)
  else name

(*TODO: MOVE*)
let name_of_binding (b:binding) = unseal b.ppname

let fresh_name (e:env) (basename:string) : Tac string =
  let vars = vars_of_env e in
  let binder_names = Tactics.map name_of_binding vars in
  _fresh_name binder_names basename 0

let fresh_bv (e : env) (basename : string) : Tac var =
  let name = fresh_name e basename in
  fresh_namedv_named name

let fresh_binder (e : env) (basename : string) (ty : typ) : Tac binder =
  let name = fresh_name e basename in
  fresh_binder_named name ty

//  let vars = vars_of_env e in
//  let binder_names = Tactics.map name_of_binding vars in
//  _fresh_var binder_names basename 0
//  let v = fresh_bv e basename in
//  mk_binder v ty

let genv_push_fresh_binder (ge : genv) (basename : string) (ty : typ) : Tac (genv & binder) =
  let b = fresh_binder ge.env basename ty in
  (* TODO: we can have a shortcircuit push (which performs less checks) *)
  let ge' = genv_push_binding ge (binder_to_binding b) true None in
  ge', b

// TODO: actually we should use push_fresh_bv more
let push_fresh_binder (e : env) (basename : string) (ty : typ) : Tac (env & binder) =
  let b = fresh_binder e basename ty in
  let e' = push_binding e (binder_to_binding b) in
  e', b

let genv_push_fresh_bv (ge : genv) (basename : string) (ty : typ) : Tac (genv & var) =
  let ge', b = genv_push_fresh_binder ge basename ty in
  ge', binder_to_namedv b

val push_fresh_var : env -> string -> typ -> Tac (term & binder & env)
let push_fresh_var e0 basename ty =
  let e1, b1 = push_fresh_binder e0 basename ty in
  let v1 = pack (Tv_Var (binder_to_namedv b1)) in
  v1, b1, e1

val genv_push_fresh_var : genv -> string -> typ -> Tac (term & binder & genv)
let genv_push_fresh_var ge0 basename ty =
  let ge1, b1 = genv_push_fresh_binder ge0 basename ty in
  let v1 = pack (Tv_Var (binder_to_namedv b1)) in
  v1, b1, ge1

val push_two_fresh_vars : env -> string -> typ -> Tac (term & binder & term & binder & env)
let push_two_fresh_vars e0 basename ty =
  let e1, b1 = push_fresh_binder e0 basename ty in
  let e2, b2 = push_fresh_binder e1 basename ty in
  let v1 = pack (Tv_Var (binder_to_namedv b1)) in
  let v2 = pack (Tv_Var (binder_to_namedv b2)) in
  v1, b1, v2, b2, e2

val genv_push_two_fresh_vars : genv -> string -> typ -> Tac (term & binder & term & binder & genv)
let genv_push_two_fresh_vars ge0 basename ty =
  let ge1, b1 = genv_push_fresh_binder ge0 basename ty in
  let ge2, b2 = genv_push_fresh_binder ge1 basename ty in
  let v1 = pack (Tv_Var (binder_to_namedv b1)) in
  let v2 = pack (Tv_Var (binder_to_namedv b2)) in
  v1, b1, v2, b2, ge2



(*** Substitutions *)
/// Substitutions

/// Custom substitutions using the normalizer. This is the easiest and safest
/// way to perform a substitution: if you want to substitute [v] with [t] in [exp],
/// just normalize [(fun v -> exp) t]. Note that this may be computationally expensive.
val norm_apply_subst : env -> term -> list ((var & typ) & term) -> Tac term
val norm_apply_subst_in_comp : env -> comp -> list ((var & typ) & term) -> Tac comp

let norm_apply_subst e t subst =
  let bl, vl = unzip subst in
  let bl = List.Tot.map (fun (v,ty) -> namedv_to_binder v ty) bl in
  let t1 = mk_abs bl t in
  let t2 = mk_e_app t1 vl in
  norm_term_env e [] t2

let norm_apply_subst_in_comp e c subst =
  let subst = (fun x -> norm_apply_subst e x subst) in
  let subst_in_aqualv a : Tac aqualv =
    match a with
    | Q_Implicit
    | Q_Explicit -> a
    | Q_Meta t -> Q_Meta (subst t)
  in
  match inspect_comp c with
  | C_Total ret ->
    let ret = subst ret in
    pack_comp (C_Total ret)
  | C_GTotal ret ->
    let ret = subst ret in
    pack_comp (C_GTotal ret)
  | C_Lemma pre post patterns ->
    let pre = subst pre in
    let post = subst post in
    let patterns = subst patterns in
    pack_comp (C_Lemma pre post patterns)
  | C_Eff us eff_name result eff_args decrs ->
    let result = subst result in
    let eff_args = map (fun (x, a) -> (subst x, subst_in_aqualv a)) eff_args in
    let decrs = map subst decrs in
    pack_comp (C_Eff us eff_name result eff_args decrs)

/// As substitution with normalization is very expensive, we implemented another
/// technique which works by exploring terms. This is super fast, but the terms
/// seem not to be reconstructed in the same way, which has a big impact on pretty printing.
/// For example, terms like [A /\ B] get printed as [Prims.l_and A B].
let subst_t = list (var & term)
val deep_apply_subst : env -> term -> subst_t -> Tac term
// Whenever we encounter a construction which introduces a binder, we need to apply
// the substitution in the binder type. Note that this gives a new binder, with
// which we need to replace the old one in what follows.
// Also note that it should be possible to rewrite [deep_apply_subst] in terms of [visit_tm],
// but [deep_apply_subst] seems to be a bit more precise with regard to type replacements (not
// sure it is really important, though).
val deep_apply_subst_in_var : env -> var -> subst_t -> Tac (var & subst_t)
val deep_apply_subst_in_binder : env -> binder -> subst_t -> Tac (binder & subst_t)
val deep_apply_subst_in_comp : env -> comp -> subst_t -> Tac comp
val deep_apply_subst_in_pattern : env -> pattern -> subst_t -> Tac (pattern & subst_t)

let rec deep_apply_subst e t subst =
  match inspect t with
  | Tv_Var b ->
    begin match bind_map_get subst b with
    | None -> t
    | Some t' -> t'
    end
  | Tv_BVar b ->
    fail "Should not happen";
    t
  | Tv_FVar _ -> t
  | Tv_App hd (a,qual) ->
    let hd = deep_apply_subst e hd subst in
    let a = deep_apply_subst e a subst in
    pack (Tv_App hd (a, qual))
  | Tv_Abs br body ->
    let body = deep_apply_subst e body subst in
    pack (Tv_Abs br body)
  | Tv_Arrow br c ->
    let br, subst = deep_apply_subst_in_binder e br subst in
    let c = deep_apply_subst_in_comp e c subst in
    pack (Tv_Arrow br c)
  | Tv_Type _ -> t
  | Tv_Refine br ref ->
    let br, subst = deep_apply_subst_in_binder e br subst in
    let ref = deep_apply_subst e ref subst in
    assume (is_simple_binder br); // trivial
    pack (Tv_Refine br ref)
  | Tv_Const _ -> t
  | Tv_Uvar _ _ -> t
  | Tv_Let recf attrs br def body ->
    (* No need to substitute in the attributes - that we filter for safety *)
    let br, subst = deep_apply_subst_in_binder e br subst in
    let def = deep_apply_subst e def subst in
    let body = deep_apply_subst e body subst in
    assume (is_simple_binder br); // trivial
    pack (Tv_Let recf [] br def body)
  | Tv_Match scrutinee ret_opt branches -> (* TODO: type of pattern variables *)
    let scrutinee = deep_apply_subst e scrutinee subst in
    let ret_opt = map_opt (fun (b, asc) ->
      let b, subst = deep_apply_subst_in_binder e b subst in
      let asc =
        match asc with
        | Inl t, tacopt, use_eq ->
          Inl (deep_apply_subst e t subst),
          map_opt (fun tac -> deep_apply_subst e tac subst) tacopt,
          use_eq
        | Inr c, tacopt, use_eq ->
          Inr (deep_apply_subst_in_comp e c subst),
          map_opt (fun tac -> deep_apply_subst e tac subst) tacopt,
          use_eq in
      b, asc) ret_opt in
    (* For the branches: we don't need to explore the patterns *)
    let deep_apply_subst_in_branch branch =
      let pat, tm = branch in
      let pat, subst = deep_apply_subst_in_pattern e pat subst in
      let tm = deep_apply_subst e tm subst in
      pat, tm
    in
    let branches = map deep_apply_subst_in_branch branches in
    pack (Tv_Match scrutinee ret_opt branches)
  | Tv_AscribedT exp ty tac use_eq ->
    let exp = deep_apply_subst e exp subst in
    let ty = deep_apply_subst e ty subst in
    (* no need to apply it on the tactic - that we filter for safety *)
    pack (Tv_AscribedT exp ty None use_eq)
  | Tv_AscribedC exp c tac use_eq ->
    let exp = deep_apply_subst e exp subst in
    let c = deep_apply_subst_in_comp e c subst in
    (* no need to apply it on the tactic - that we filter for safety *)
    pack (Tv_AscribedC exp c None use_eq)
  | _ ->
    (* Unknown *)
    t

and deep_apply_subst_in_bv e bv subst =
  (* No substitution needs to happen for variables
    (there is no longer a sort). But, shift the substitution. *)
  bv, (bv, pack (Tv_Var bv))::subst

(*
 * AR: TODO: should apply subst in attrs?
 *)
and deep_apply_subst_in_binder e br subst =
  let sort = deep_apply_subst e br.sort subst in
  let v = binder_to_namedv br in
  let subst = (v, pack (Tv_Var v)) :: subst in // shift
  let br = {
    sort   = sort;

    ppname = br.ppname;
    uniq   = br.uniq;
    qual   = br.qual;
    attrs  = br.attrs;
  }
  in
  br, subst

and deep_apply_subst_in_comp e c subst =
  let subst = (fun x -> deep_apply_subst e x subst) in
  let subst_in_aqualv a : Tac aqualv =
    match a with
    | Q_Implicit
    | Q_Explicit -> a
    | Q_Meta t -> Q_Meta (subst t)
  in
  match inspect_comp c with
  | C_Total ret ->
    let ret = subst ret in
    pack_comp (C_Total ret)
  | C_GTotal ret ->
    let ret = subst ret in
    pack_comp (C_GTotal ret)
  | C_Lemma pre post patterns ->
    let pre = subst pre in
    let post = subst post in
    let patterns = subst patterns in
    pack_comp (C_Lemma pre post patterns)
  | C_Eff us eff_name result eff_args decrs ->
    let result = subst result in
    let eff_args = map (fun (x, a) -> (subst x, subst_in_aqualv a)) eff_args in
    let decrs = map subst decrs in
    pack_comp (C_Eff us eff_name result eff_args decrs)

and deep_apply_subst_in_pattern e pat subst =
  match pat with
  | Pat_Constant _ -> pat, subst
  | Pat_Cons {head=fv; univs=us; subpats=patterns} ->
    (* The types of the variables in the patterns should be independent of each
     * other: we use fold_left only to incrementally update the substitution *)
    let patterns, subst =
      fold_right (fun (pat, b) (pats, subst) ->
                      let pat, subst = deep_apply_subst_in_pattern e pat subst in
                      ((pat, b) :: pats, subst)) patterns ([], subst)
    in
    Pat_Cons {head=fv; univs=us; subpats=patterns}, subst
  | Pat_Var {v; sort} ->
    let st = Sealed.seal (deep_apply_subst e (unseal sort) subst) in
    let v, subst = deep_apply_subst_in_bv e v subst in
    Pat_Var {v; sort}, subst
  | Pat_Dot_Term {t} ->
    Pat_Dot_Term {t=map_opt (fun t -> deep_apply_subst e t subst) t}, subst

/// The substitution functions actually used in the rest of the meta F* functions.
/// For now, we use normalization because even though it is sometimes slow it
/// gives prettier terms, and readability is the priority. In order to mitigate
/// the performance issue, we try to minimize the number of calls to those functions,
/// by doing lazy instantiations for example (rather than incrementally apply
/// substitutions in a term, accumulate the substitutions and perform them all at once).
/// TODO: would it be good to have a native substitution function in F*
let apply_subst = norm_apply_subst
let apply_subst_in_comp = norm_apply_subst_in_comp

val opt_apply_subst : env -> option term -> list ((var & typ) & term) -> Tac (option term)
let opt_apply_subst e opt_t subst =
  match opt_t with
  | None -> None
  | Some t -> Some (apply_subst e t subst)

(*** Variable shadowing *)
/// Introduce fresh variables to generate a substitution for the variables shadowed
/// in the current environment.
val generate_shadowed_subst : genv -> Tac (genv & list (var & typ & var))

/// In order to introduce variables with coherent types (the variables' types
/// may be dependent) and make things simpler, we build one big term:
/// [> (fun x1 x2 ... xn -> ())
/// Then, for each variable, we introduce a fresh variable with the same type as
/// the outermost abstraction, apply the above term to this new variable and
/// normalize to "apply" the substitution and reveal the next binding.

let rec _generate_shadowed_subst (ge:genv) (t:term) (bvl : list (var & typ)) :
  Tac (genv & list (var & typ & var)) =
  match bvl with
  | [] -> ge, []
  | old_bv :: bvl' ->
    match inspect t with
    | Tv_Abs b _ ->
      (* Introduce the new binder *)
      let ty = b.sort in
      let name = unseal b.ppname in
      let ge1, fresh = genv_push_fresh_bv ge ("__" ^ name) ty in
      let t1 = mk_e_app t [pack (Tv_Var fresh)] in
      let t2 = norm_term_env ge1.env [] t1 in
      (* Recursion *)
      let ge2, nbvl = _generate_shadowed_subst ge1 t2 bvl' in
      (* Return *)
      ge2, (fst old_bv, ty, fresh) :: nbvl
    | _ -> mfail "_subst_with_fresh_vars: not a Tv_Abs"

let generate_shadowed_subst ge =
  (* We need to replace the variables starting with the oldest *)
  let bvl = List.Tot.rev ge.svars in
  let bl = List.Tot.map (fun (bv, sort) -> namedv_to_binder bv sort) bvl in
  let dummy = mk_abs bl (`()) in
  _generate_shadowed_subst ge dummy bvl
