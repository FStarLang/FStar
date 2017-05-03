module FStar.Syntax.Base

open FStar.Order

assume type term

assume type bv
assume type fv
assume type binder
assume type env

type name    = list string
type typ     = term
type binders = list binder

noeq
type const =
  | C_Unit : const
  | C_Int : int -> const // Not exposing the details, I presume
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


// TODO: cleanup assume/let, makes no sense but the compiler currently expects __ versions
// or maybe leave as it for better maintanibility...
// "every problem in computer science is solved by adding another level of indirection"
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

assume private val __type_of_binder: binder -> term
let type_of_binder (b:binder) : term = __type_of_binder b

assume private val __term_eq : term -> term -> bool
let term_eq t1 t2 : bool = __term_eq t1 t2

assume val __inspect : term -> term_view
let inspect t : term_view = __inspect t

assume val __pack : term_view -> term
let pack tv : term = __pack tv

assume val __term_to_string : term -> string
let term_to_string t : string = __term_to_string t

val flatten_name : name -> Tot string
let rec flatten_name ns =
    match ns with
    | [] -> ""
    | [n] -> n
    | n::ns -> n ^ "." ^ flatten_name ns

let imp_qn = ["Prims"; "l_imp"]
let and_qn = ["Prims"; "l_and"]
let or_qn  = ["Prims"; "l_or"]
let not_qn = ["Prims"; "l_not"]
