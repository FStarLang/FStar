module FStar.Reflection.Syntax

open FStar.Order

open FStar.Reflection.Types

type name    = list string
type typ     = term
type binders = list binder

noeq
type const =
  | C_Unit : const
  | C_Int : int -> const // Not exposing the details, I presume
  | C_True : const
  | C_False : const
  (* TODO: complete *)

noeq
type term_view =
  | Tv_Var    : binder -> term_view
  | Tv_FVar   : fv -> term_view
  | Tv_App    : term -> term -> term_view
  | Tv_Abs    : binder -> term -> term_view
  | Tv_Arrow  : binder -> term -> term_view
  | Tv_Type   : unit -> term_view
  | Tv_Refine : binder -> term -> term_view
  | Tv_Const  : const -> term_view
  | Tv_Unknown : term_view // Baked in "None"
  (* TODO: complete *)

assume private val __type_of_binder: binder -> term
let type_of_binder (b:binder) : term = __type_of_binder b

(* Comparison of a term_view to term. Allows to recurse while changing the view *)
val smaller : term_view -> term -> Type0
let smaller tv t =
    match tv with
    | Tv_App l r ->
        l << t /\ r << t

    | Tv_Abs b t'
    | Tv_Arrow b t'
    | Tv_Refine b t' ->
        type_of_binder b << t /\ t' << t

    | Tv_Type _
    | Tv_Const _
    | Tv_Unknown
    | Tv_Var _
    | Tv_FVar _ -> True

(* The main characters *)
assume val __inspect : t:term -> tv:term_view{smaller tv t}
let inspect t : term_view = __inspect t

assume val __pack : term_view -> term
let pack tv : term = __pack tv

(* They are inverses *)
assume val pack_inspect_inv : (t:term) -> Lemma (pack (inspect t) == t)
assume val inspect_pack_inv : (tv:term_view) -> Lemma (inspect (pack tv) == tv)

assume val __inspect_fv : fv -> name
let inspect_fv (fv:fv) = __inspect_fv fv

assume val __pack_fv : name -> fv
let pack_fv (ns:name) = __pack_fv ns

assume val __compare_binder : binder -> binder -> order
let compare_binder (b1:binder) (b2:binder) = __compare_binder b1 b2

assume val __inspect_bv : binder -> string
let inspect_bv (b:binder) = __inspect_bv b

assume private val __binders_of_env : env -> binders
let binders_of_env (e:env) : binders = __binders_of_env e

assume private val __is_free : binder -> term -> bool
let is_free (b:binder) (t:term) : bool = __is_free b t

assume private val __term_eq : term -> term -> bool
let term_eq t1 t2 : bool = __term_eq t1 t2

assume val __term_to_string : term -> string
let term_to_string t : string = __term_to_string t

assume val __fresh_binder : typ -> binder
let fresh_binder t : binder = __fresh_binder t

val flatten_name : name -> Tot string
let rec flatten_name ns =
    match ns with
    | [] -> ""
    | [n] -> n
    | n::ns -> n ^ "." ^ flatten_name ns


// TODO: these are awful names
let imp_qn       = ["Prims"; "l_imp"]
let and_qn       = ["Prims"; "l_and"]
let or_qn        = ["Prims"; "l_or"]
let not_qn       = ["Prims"; "l_not"]
let iff_qn       = ["Prims"; "l_iff"]
let eq2_qn       = ["Prims"; "eq2"]
let eq1_qn       = ["Prims"; "eq"]
let true_qn      = ["Prims"; "l_True"]
let false_qn     = ["Prims"; "l_False"]
let b2t_qn       = ["Prims"; "b2t"]
let forall_qn    = ["Prims"; "l_Forall"]
let squash_qn    = ["Prims"; "squash"]

let bool_true_qn  = ["Prims"; "true"]
let bool_false_qn = ["Prims"; "false"]

let int_lid      = ["Prims"; "int"]
let bool_lid     = ["Prims"; "bool"]
let unit_lid     = ["Prims"; "unit"]

let add_qn       = ["Prims"; "op_Addition"]
let neg_qn       = ["Prims"; "op_Minus"]
let minus_qn     = ["Prims"; "op_Subtraction"]
let mult_qn      = ["Prims"; "op_Multiply"]
let mult'_qn     = ["FStar"; "Mul"; "op_Star"]
let div_qn       = ["Prims"; "op_Division"]
let lt_qn        = ["Prims"; "op_LessThan"]
let lte_qn       = ["Prims"; "op_LessThanOrEqual"]
let gt_qn        = ["Prims"; "op_GreaterThan"]
let gte_qn       = ["Prims"; "op_GreaterThanOrEqual"]
let mod_qn       = ["Prims"; "op_Modulus"]

(* Helpers for dealing with nested applications *)
let rec collect_app' (args : list term) (t : term) : Tot (term * list term) (decreases t) =
    match inspect t with
    | Tv_App l r ->
        collect_app' (r::args) l
    | _ -> (t, args)

val collect_app : term -> term * list term
let collect_app = collect_app' []

let rec mk_app (t : term) (args : list term) : Tot term (decreases args) =
    match args with
    | [] -> t
    | (x::xs) -> mk_app (pack (Tv_App t x)) xs

// TODO: move away
let rec eqlist (f : 'a -> 'a -> bool) (xs : list 'a) (ys : list 'a) : Tot bool =
    match xs, ys with
    | [], [] -> true
    | x::xs, y::ys -> f x y && eqlist f xs ys
    | _ -> false

let fv_to_string (fv:fv) : string = String.concat "." (inspect_fv fv)

noeq
type norm_step =
    | Simpl
    | WHNF
    | Primops
    | Delta

let compare_fv (f1 f2 : fv) : order =
    compare_list (fun s1 s2 -> order_from_int (String.compare s1 s2)) (inspect_fv f1) (inspect_fv f2)

let rec compare_const (c1 c2 : const) : order =
    match c1, c2 with
    | C_Unit, C_Unit -> Eq
    | C_Int i, C_Int j -> order_from_int (i - j)
    | C_True, C_True -> Eq
    | C_False, C_False -> Eq
    | C_Unit,  _ -> Lt   | _, C_Unit  -> Gt
    | C_Int _, _ -> Lt   | _, C_Int _ -> Gt
    | C_True,  _ -> Lt   | _, C_True  -> Gt
    | C_False, _ -> Lt   | _, C_False -> Gt

let rec compare_term (s t : term) : order =
    match inspect s, inspect t with
    | Tv_Var sv, Tv_Var tv ->
        compare_binder sv tv

    | Tv_FVar sv, Tv_FVar tv ->
        compare_fv sv tv

    | Tv_App h1 a1, Tv_App h2 a2 ->
        lex (compare_term h1 h2) (fun () -> compare_term a1 a2)

    | Tv_Abs b1 e1, Tv_Abs b2 e2
    | Tv_Arrow b1 e1, Tv_Arrow b2 e2
    | Tv_Refine b1 e1, Tv_Refine b2 e2 ->
        lex (compare_binder b1 b2) (fun () -> compare_term e1 e2)

    | Tv_Type (), Tv_Type () ->
        Eq

    | Tv_Const c1, Tv_Const c2 ->
        compare_const c1 c2

    | Tv_Unknown, Tv_Unknown ->
        Eq

    // From here onwards, they must have different constructors. Order them arbitrarilly as in the definition.
    | Tv_Var _, _      -> Lt   | _, Tv_Var _      -> Gt
    | Tv_FVar _, _     -> Lt   | _, Tv_FVar _     -> Gt
    | Tv_App _ _, _    -> Lt   | _, Tv_App _ _    -> Gt
    | Tv_Abs _ _, _    -> Lt   | _, Tv_Abs _ _    -> Gt
    | Tv_Arrow _ _, _  -> Lt   | _, Tv_Arrow _ _  -> Gt
    | Tv_Type (), _    -> Lt   | _, Tv_Type ()    -> Gt
    | Tv_Refine _ _, _ -> Lt   | _, Tv_Refine _ _ -> Gt
    | Tv_Const _, _    -> Lt   | _, Tv_Const _    -> Gt
    | Tv_Unknown, _    -> Lt   | _, Tv_Unknown    -> Gt
