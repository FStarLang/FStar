open Prims
open FStar_Tactics_Types
type name = Prims.string Prims.list
type typ = term
type binders = binder Prims.list
type goal = (env* term)
type goals = goal Prims.list
type state = (goals* goals)
type formula =
  | True_
  | False_
  | Eq of typ* term* term
  | And of term* term
  | Or of term* term
  | Not of term
  | Implies of term* term
  | Iff of term* term
  | Forall of binders* term
  | Exists of binders* term
  | App of term* term
  | Name of binder
  | IntLit of Prims.int
let uu___is_True_: formula -> Prims.bool =
  fun projectee  -> match projectee with | True_  -> true | uu____73 -> false
let uu___is_False_: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | False_  -> true | uu____79 -> false
let uu___is_Eq: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Eq (_0,_1,_2) -> true | uu____91 -> false
let __proj__Eq__item___0: formula -> typ =
  fun projectee  -> match projectee with | Eq (_0,_1,_2) -> _0
let __proj__Eq__item___1: formula -> term =
  fun projectee  -> match projectee with | Eq (_0,_1,_2) -> _1
let __proj__Eq__item___2: formula -> term =
  fun projectee  -> match projectee with | Eq (_0,_1,_2) -> _2
let uu___is_And: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | And (_0,_1) -> true | uu____143 -> false
let __proj__And__item___0: formula -> term =
  fun projectee  -> match projectee with | And (_0,_1) -> _0
let __proj__And__item___1: formula -> term =
  fun projectee  -> match projectee with | And (_0,_1) -> _1
let uu___is_Or: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Or (_0,_1) -> true | uu____177 -> false
let __proj__Or__item___0: formula -> term =
  fun projectee  -> match projectee with | Or (_0,_1) -> _0
let __proj__Or__item___1: formula -> term =
  fun projectee  -> match projectee with | Or (_0,_1) -> _1
let uu___is_Not: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Not _0 -> true | uu____209 -> false
let __proj__Not__item___0: formula -> term =
  fun projectee  -> match projectee with | Not _0 -> _0
let uu___is_Implies: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Implies (_0,_1) -> true | uu____229 -> false
let __proj__Implies__item___0: formula -> term =
  fun projectee  -> match projectee with | Implies (_0,_1) -> _0
let __proj__Implies__item___1: formula -> term =
  fun projectee  -> match projectee with | Implies (_0,_1) -> _1
let uu___is_Iff: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Iff (_0,_1) -> true | uu____263 -> false
let __proj__Iff__item___0: formula -> term =
  fun projectee  -> match projectee with | Iff (_0,_1) -> _0
let __proj__Iff__item___1: formula -> term =
  fun projectee  -> match projectee with | Iff (_0,_1) -> _1
let uu___is_Forall: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Forall (_0,_1) -> true | uu____297 -> false
let __proj__Forall__item___0: formula -> binders =
  fun projectee  -> match projectee with | Forall (_0,_1) -> _0
let __proj__Forall__item___1: formula -> term =
  fun projectee  -> match projectee with | Forall (_0,_1) -> _1
let uu___is_Exists: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Exists (_0,_1) -> true | uu____331 -> false
let __proj__Exists__item___0: formula -> binders =
  fun projectee  -> match projectee with | Exists (_0,_1) -> _0
let __proj__Exists__item___1: formula -> term =
  fun projectee  -> match projectee with | Exists (_0,_1) -> _1
let uu___is_App: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | App (_0,_1) -> true | uu____365 -> false
let __proj__App__item___0: formula -> term =
  fun projectee  -> match projectee with | App (_0,_1) -> _0
let __proj__App__item___1: formula -> term =
  fun projectee  -> match projectee with | App (_0,_1) -> _1
let uu___is_Name: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | Name _0 -> true | uu____397 -> false
let __proj__Name__item___0: formula -> binder =
  fun projectee  -> match projectee with | Name _0 -> _0
let uu___is_IntLit: formula -> Prims.bool =
  fun projectee  ->
    match projectee with | IntLit _0 -> true | uu____415 -> false
let __proj__IntLit__item___0: formula -> Prims.int =
  fun projectee  -> match projectee with | IntLit _0 -> _0
type const =
  | C_Unit
  | C_Int of Prims.int
let uu___is_C_Unit: const -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Unit  -> true | uu____434 -> false
let uu___is_C_Int: const -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____442 -> false
let __proj__C_Int__item___0: const -> Prims.int =
  fun projectee  -> match projectee with | C_Int _0 -> _0
type term_view =
  | Tv_Var of binder
  | Tv_FVar of fv
  | Tv_App of term* term
  | Tv_Abs of binder* term
  | Tv_Arrow of binder* term
  | Tv_Type of Prims.unit
  | Tv_Refine of binder* term
  | Tv_Const of const
let uu___is_Tv_Var: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Var _0 -> true | uu____496 -> false
let __proj__Tv_Var__item___0: term_view -> binder =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0
let uu___is_Tv_FVar: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____514 -> false
let __proj__Tv_FVar__item___0: term_view -> fv =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0
let uu___is_Tv_App: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_App (_0,_1) -> true | uu____534 -> false
let __proj__Tv_App__item___0: term_view -> term =
  fun projectee  -> match projectee with | Tv_App (_0,_1) -> _0
let __proj__Tv_App__item___1: term_view -> term =
  fun projectee  -> match projectee with | Tv_App (_0,_1) -> _1
let uu___is_Tv_Abs: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Abs (_0,_1) -> true | uu____568 -> false
let __proj__Tv_Abs__item___0: term_view -> binder =
  fun projectee  -> match projectee with | Tv_Abs (_0,_1) -> _0
let __proj__Tv_Abs__item___1: term_view -> term =
  fun projectee  -> match projectee with | Tv_Abs (_0,_1) -> _1
let uu___is_Tv_Arrow: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Arrow (_0,_1) -> true | uu____602 -> false
let __proj__Tv_Arrow__item___0: term_view -> binder =
  fun projectee  -> match projectee with | Tv_Arrow (_0,_1) -> _0
let __proj__Tv_Arrow__item___1: term_view -> term =
  fun projectee  -> match projectee with | Tv_Arrow (_0,_1) -> _1
let uu___is_Tv_Type: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____634 -> false
let __proj__Tv_Type__item___0: term_view -> Prims.unit = fun projectee  -> ()
let uu___is_Tv_Refine: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Refine (_0,_1) -> true | uu____654 -> false
let __proj__Tv_Refine__item___0: term_view -> binder =
  fun projectee  -> match projectee with | Tv_Refine (_0,_1) -> _0
let __proj__Tv_Refine__item___1: term_view -> term =
  fun projectee  -> match projectee with | Tv_Refine (_0,_1) -> _1
let uu___is_Tv_Const: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____686 -> false
let __proj__Tv_Const__item___0: term_view -> const =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0
let __inspect_fv: fv -> name =
  Obj.magic (fun uu____701  -> failwith "Not yet implemented:__inspect_fv")
let inspect_fv: fv -> name = fun fv  -> __inspect_fv fv
let __pack_fv: name -> fv =
  Obj.magic (fun uu____710  -> failwith "Not yet implemented:__pack_fv")
let pack_fv: name -> fv = fun ns  -> __pack_fv ns
let __compare_binder: binder -> binder -> FStar_Order.order =
  Obj.magic
    (fun uu____723  ->
       fun uu____724  -> failwith "Not yet implemented:__compare_binder")
let compare_binder: binder -> binder -> FStar_Order.order =
  fun b1  -> fun b2  -> __compare_binder b1 b2
let __inspect_bv: binder -> Prims.string =
  Obj.magic (fun uu____737  -> failwith "Not yet implemented:__inspect_bv")
let inspect_bv: binder -> Prims.string = fun b  -> __inspect_bv b
let rec flatten_name: name -> Prims.string =
  fun ns  ->
    match ns with
    | [] -> ""
    | n::[] -> n
    | n::ns1 -> Prims.strcat n (Prims.strcat "." (flatten_name ns1))
type 'Aa __result =
  | Success of 'Aa* state
  | Failed of Prims.string* state
let uu___is_Success projectee =
  match projectee with | Success (_0,_1) -> true | uu____786 -> false
let __proj__Success__item___0 projectee =
  match projectee with | Success (_0,_1) -> _0
let __proj__Success__item___1 projectee =
  match projectee with | Success (_0,_1) -> _1
let uu___is_Failed projectee =
  match projectee with | Failed (_0,_1) -> true | uu____842 -> false
let __proj__Failed__item___0 projectee =
  match projectee with | Failed (_0,_1) -> _0
let __proj__Failed__item___1 projectee =
  match projectee with | Failed (_0,_1) -> _1
type 'Aa __tac = state -> 'Aa __result
let __ret x s = Success (x, s)
let __bind t1 t2 p =
  match t1 p with
  | Success (a,q) -> t2 a q
  | Failed (msg,q) -> Failed (msg, q)
let __get: Prims.unit -> state -> state __result =
  fun uu____969  -> fun s0  -> Success (s0, s0)
type 'Aa __tac_wp = state -> Prims.unit -> Obj.t
type ('Aa,'Ab,'Awp,'Af,'Aps,'Apost) g_bind = 'Awp
type ('Aa,'Awp) g_compact = Prims.unit
type ('Ar,'Aa,'Ab,'Awp,'Af) __TAC_eff_override_bind_wp = Prims.unit
type ('Aa,'Awp,'As,'Ap') _dm4f_TAC_lift_from_pure = 'Awp
type ('Aa,'Ax,'As,'Ap') _dm4f_TAC_return_wp = 'Ap'
let _dm4f_TAC_return_elab x s = Success (x, s)
let _dm4f_TAC_bind_elab t1 t2__w t2 p =
  match t1 p with
  | Success (a,q) -> t2 a q
  | Failed (msg,q) -> Failed (msg, q)
let _dm4f_TAC___proj__TAC__item____get_elab:
  Prims.unit ->
    ((env* term) Prims.list* (env* term) Prims.list) ->
      ((env* term) Prims.list* (env* term) Prims.list) __result
  = fun uu____1337  -> fun s0  -> Success (s0, s0)
type _dm4f_TAC___proj__TAC__item____get_complete_type =
  Prims.unit ->
    ((env* term) Prims.list* (env* term) Prims.list) ->
      ((env* term) Prims.list* (env* term) Prims.list) __result
type ('Aa,'Awp_a) _dm4f_TAC_repr =
  ((env* term) Prims.list* (env* term) Prims.list) -> 'Aa __result
type _dm4f_TAC_pre =
  ((env* term) Prims.list* (env* term) Prims.list) -> Obj.t
type 'Aa _dm4f_TAC_post = 'Aa __result -> Obj.t
type 'Aa _dm4f_TAC_wp =
  ((env* term) Prims.list* (env* term) Prims.list) -> Prims.unit -> Obj.t
type ('Aa,'At) _dm4f_TAC_ctx =
  ((env* term) Prims.list* (env* term) Prims.list) -> Prims.unit -> 'At
type ('Aa,'At) _dm4f_TAC_gctx =
  ((env* term) Prims.list* (env* term) Prims.list) -> Prims.unit -> 'At
let _dm4f_TAC_pure x uu____1554 uu____1555 = x
let _dm4f_TAC_app l r uu____1671 uu____1672 = Obj.magic ()
let _dm4f_TAC_lift1 f a1 uu____1775 uu____1776 = Obj.magic ()
let _dm4f_TAC_lift2 f a1 a2 uu____1897 uu____1898 = Obj.magic ()
let _dm4f_TAC_push f uu____2028 uu____2029 e1 = Obj.magic ()
type ('Aa,'Ac,'Auu____2066,'Auu____2067,'Auu____2068,'Auu____2069) _dm4f_TAC_wp_if_then_else =
  Prims.unit
type ('Aa,'Aq,'Awp,'Auu____2090,'Auu____2091) _dm4f_TAC_wp_assert =
  Prims.unit
type ('Aa,'Aq,'Awp,'Auu____2107,'Auu____2108) _dm4f_TAC_wp_assume =
  Prims.unit
type ('Aa,'Ab,'Af,'Auu____2125,'Auu____2126) _dm4f_TAC_wp_close = Prims.unit
type ('Aa,'Awp1,'Awp2) _dm4f_TAC_stronger = Prims.unit
type ('Aa,'Awp,'Auu____2183,'Auu____2184) _dm4f_TAC_wp_ite = Prims.unit
type ('Aa,'Auu____2211,'Auu____2212) _dm4f_TAC_null_wp = Prims.unit
type ('Aa,'Awp) _dm4f_TAC_wp_trivial = Prims.unit
let __proj__TAC__item__return = _dm4f_TAC_return_elab
let __proj__TAC__item__bind = _dm4f_TAC_bind_elab
let __proj__TAC__item____get uu____2289 s0 = Success (s0, s0)
type 'Aa tactic = Prims.unit -> ('Aa,Prims.unit) _dm4f_TAC_repr
let return x uu____2375 s = Success (x, s)
let bind t f uu____2423 p =
  match (t ()) p with
  | Success (a,q) -> (f a ()) q
  | Failed (msg,q) -> Failed (msg, q)
let rec fix ff u = ff (fix ff) ()
let rec fix1 ff x u = ff (fix1 ff) x ()
let __fail msg s0 = Failed (msg, s0)
let fail msg uu____2656 = __fail msg
let reify_tactic t s = (t ()) s
let trytac t uu____2711 ps =
  match reify_tactic t ps with
  | Success (a,ps') -> Success ((Some a), ps')
  | Failed (uu____2732,uu____2733) -> Success (None, ps)
let or_else t1 t2 =
  bind (trytac t1)
    (fun r  -> match r with | Some x -> return x | None  -> t2)
let __binders_of_env: env -> binders =
  Obj.magic
    (fun uu____2794  -> failwith "Not yet implemented:__binders_of_env")
let binders_of_env:
  env ->
    Prims.unit ->
      ((env* term) Prims.list* (env* term) Prims.list) -> binders __result
  = fun e  -> fun uu____2804  -> fun s  -> Success ((__binders_of_env e), s)
let __type_of_binder: binder -> term =
  Obj.magic
    (fun uu____2820  -> failwith "Not yet implemented:__type_of_binder")
let type_of_binder:
  binder ->
    Prims.unit ->
      ((env* term) Prims.list* (env* term) Prims.list) -> term __result
  = fun b  -> fun uu____2830  -> fun s  -> Success ((__type_of_binder b), s)
let __term_eq: term -> term -> Prims.bool =
  Obj.magic
    (fun uu____2850  ->
       fun uu____2851  -> failwith "Not yet implemented:__term_eq")
let term_eq:
  term ->
    term ->
      Prims.unit ->
        ((env* term) Prims.list* (env* term) Prims.list) ->
          Prims.bool __result
  =
  fun t1  ->
    fun t2  -> fun uu____2865  -> fun s  -> Success ((__term_eq t1 t2), s)
let __embed =
  Obj.magic (fun uu____2887  -> failwith "Not yet implemented:__embed")
let quote x uu____2902 s = Success ((__embed x), s)
let __term_as_formula: term -> formula Prims.option =
  Obj.magic
    (fun uu____2919  -> failwith "Not yet implemented:__term_as_formula")
let term_as_formula:
  term ->
    Prims.unit ->
      ((env* term) Prims.list* (env* term) Prims.list) ->
        formula Prims.option __result
  = fun t  -> fun uu____2932  -> fun s  -> Success ((__term_as_formula t), s)
let __inspect: term -> term_view Prims.option =
  Obj.magic (fun uu____2953  -> failwith "Not yet implemented:__inspect")
let inspect: term -> Prims.unit -> (term_view,Prims.unit) _dm4f_TAC_repr =
  fun t  ->
    fun uu____2965  ->
      match __inspect t with
      | Some tv -> (fun s  -> Success (tv, s))
      | None  -> fail "inspect failed, possibly unknown syntax" ()
let __pack: term_view -> term =
  Obj.magic (fun uu____2985  -> failwith "Not yet implemented:__pack")
let pack:
  term_view ->
    Prims.unit ->
      ((env* term) Prims.list* (env* term) Prims.list) -> term __result
  = fun tv  -> fun uu____2995  -> fun s  -> Success ((__pack tv), s)
let __term_to_string: term -> Prims.string =
  Obj.magic
    (fun uu____3011  -> failwith "Not yet implemented:__term_to_string")
let term_to_string:
  term ->
    Prims.unit ->
      ((env* term) Prims.list* (env* term) Prims.list) ->
        Prims.string __result
  = fun t  -> fun uu____3021  -> fun s  -> Success ((__term_to_string t), s)
let __forall_intros: binders __tac =
  Obj.magic
    (fun uu____3040  -> failwith "Not yet implemented:__forall_intros")
let forall_intros: Prims.unit -> binders __tac =
  fun uu____3066  -> __forall_intros
let __implies_intro: binder __tac =
  Obj.magic
    (fun uu____3076  -> failwith "Not yet implemented:__implies_intro")
let implies_intro: Prims.unit -> binder __tac =
  fun uu____3102  -> __implies_intro
let __trivial: Prims.unit __tac =
  Obj.magic (fun uu____3112  -> failwith "Not yet implemented:__trivial")
let trivial: Prims.unit -> Prims.unit __tac = fun uu____3138  -> __trivial
let __revert: Prims.unit __tac =
  Obj.magic (fun uu____3148  -> failwith "Not yet implemented:__revert")
let revert: Prims.unit -> Prims.unit __tac = fun uu____3174  -> __revert
let __clear: Prims.unit __tac =
  Obj.magic (fun uu____3184  -> failwith "Not yet implemented:__clear")
let clear: Prims.unit -> Prims.unit __tac = fun uu____3210  -> __clear
let __split: Prims.unit __tac =
  Obj.magic (fun uu____3220  -> failwith "Not yet implemented:__split")
let split: Prims.unit -> Prims.unit __tac = fun uu____3246  -> __split
let __merge: Prims.unit __tac =
  Obj.magic (fun uu____3256  -> failwith "Not yet implemented:__merge")
let merge: Prims.unit -> Prims.unit __tac = fun uu____3282  -> __merge
let __rewrite: binder -> Prims.unit __tac =
  Obj.magic (fun uu____3294  -> failwith "Not yet implemented:__rewrite")
let rewrite: binder -> Prims.unit -> Prims.unit __tac =
  fun b  -> fun uu____3305  -> __rewrite b
let __smt: Prims.unit __tac =
  Obj.magic (fun uu____3315  -> failwith "Not yet implemented:__smt")
let smt: Prims.unit -> Prims.unit __tac = fun uu____3341  -> __smt
let __visit: Prims.unit __tac -> Prims.unit __tac =
  Obj.magic (fun uu____3358  -> failwith "Not yet implemented:__visit")
let visit: Prims.unit tactic -> Prims.unit -> Prims.unit __tac =
  fun f  -> fun uu____3380  -> __visit (reify_tactic f)
let __focus: Prims.unit __tac -> Prims.unit __tac =
  Obj.magic (fun uu____3407  -> failwith "Not yet implemented:__focus")
let focus: Prims.unit tactic -> Prims.unit -> Prims.unit __tac =
  fun f  -> fun uu____3429  -> __focus (reify_tactic f)
let __seq: Prims.unit __tac -> Prims.unit __tac -> Prims.unit __tac =
  Obj.magic
    (fun uu____3463  ->
       fun uu____3464  -> failwith "Not yet implemented:__seq")
let seq:
  Prims.unit tactic -> Prims.unit tactic -> Prims.unit -> Prims.unit __tac =
  fun f  ->
    fun g  -> fun uu____3499  -> __seq (reify_tactic f) (reify_tactic g)
let __exact: term -> Prims.unit __tac =
  Obj.magic (fun uu____3529  -> failwith "Not yet implemented:__exact")
let exact: term -> Prims.unit -> Prims.unit __tac =
  fun t  -> fun uu____3540  -> __exact t
let __apply_lemma: term -> Prims.unit __tac =
  Obj.magic (fun uu____3552  -> failwith "Not yet implemented:__apply_lemma")
let apply_lemma:
  term tactic ->
    Prims.unit ->
      ((env* term) Prims.list* (env* term) Prims.list) -> Prims.unit __result
  =
  fun t  ->
    fun uu____3572  ->
      fun p  ->
        match (t ()) p with
        | Success (a,q) -> __apply_lemma a q
        | Failed (msg,q) -> Failed (msg, q)
let __print: Prims.string -> Prims.unit __tac =
  Obj.magic (fun uu____3634  -> failwith "Not yet implemented:__print")
let print: Prims.string -> Prims.unit -> Prims.unit __tac =
  fun msg  -> fun uu____3645  -> __print msg
let __dump: Prims.string -> Prims.unit __tac =
  Obj.magic (fun uu____3657  -> failwith "Not yet implemented:__dump")
let dump: Prims.string -> Prims.unit -> Prims.unit __tac =
  fun msg  -> fun uu____3668  -> __dump msg
let __grewrite: term -> term -> Prims.unit __tac =
  Obj.magic
    (fun uu____3684  ->
       fun uu____3685  -> failwith "Not yet implemented:__grewrite")
let grewrite: term -> term -> Prims.unit -> Prims.unit __tac =
  fun t1  -> fun t2  -> fun uu____3700  -> __grewrite t1 t2
let rec revert_all: binders -> Prims.unit tactic =
  fun bs  ->
    match bs with
    | [] -> return ()
    | uu____3715::tl -> bind revert (fun uu___7_3722  -> revert_all tl)
let get:
  Prims.unit -> (state,(state __result,Obj.t) Prims.l_Forall) _dm4f_TAC_repr
  = Obj.magic (fun uu____3746  -> __proj__TAC__item____get ())
let cur_goal: goal tactic =
  bind get
    (fun ps  ->
       match ps with
       | (goals,uu____3762) ->
           (match goals with
            | [] -> fail "No more goals"
            | hd::uu____3767 -> return hd))
let destruct_equality_implication:
  term -> (formula* term) Prims.option tactic =
  fun t  ->
    bind (term_as_formula t)
      (fun f  ->
         match f with
         | Some (Implies (lhs,rhs)) ->
             bind (term_as_formula lhs)
               (fun lhs1  ->
                  match f with
                  | Some (Eq (uu____3832,uu____3833,uu____3834)) ->
                      return (Some ((Prims.__proj__Some__item__v lhs1), rhs))
                  | uu____3842 -> return None)
         | uu____3851 -> return None)
let rec user_visit:
  Prims.unit tactic -> Prims.unit -> (Prims.unit,Prims.unit) _dm4f_TAC_repr =
  fun callback  -> fun u  -> or_else callback (user_visit callback) ()
let rec simplify_eq_implication:
  Prims.unit -> (Prims.unit,Prims.unit) _dm4f_TAC_repr =
  fun u  ->
    bind cur_goal
      (fun g  ->
         match g with
         | (context,goal_t) ->
             bind (destruct_equality_implication goal_t)
               (fun r  ->
                  match r with
                  | None  -> fail "Not an equality implication"
                  | Some (uu____3988,rhs) ->
                      bind implies_intro
                        (fun eq_h  ->
                           bind (rewrite eq_h)
                             (fun uu___9_4005  ->
                                bind clear
                                  (fun uu___8_4008  ->
                                     user_visit simplify_eq_implication)))))
      ()
let rec try_rewrite_equality: term -> binders -> Prims.unit tactic =
  fun x  ->
    fun bs  ->
      match bs with
      | [] -> return ()
      | x_t::bs1 ->
          bind (type_of_binder x_t)
            (fun t  ->
               bind (term_as_formula t)
                 (fun f  ->
                    match f with
                    | Some (Eq (uu____4056,y,uu____4058)) ->
                        bind (term_eq x y)
                          (fun b  ->
                             if b
                             then rewrite x_t
                             else try_rewrite_equality x bs1)
                    | uu____4074 -> try_rewrite_equality x bs1))
let rec rewrite_all_context_equalities: binders -> Prims.unit tactic =
  fun bs  ->
    match bs with
    | [] -> return ()
    | x_t::bs1 ->
        bind (type_of_binder x_t)
          (fun tx  ->
             bind (term_as_formula tx)
               (fun f  ->
                  match f with
                  | Some (Eq (uu____4120,uu____4121,uu____4122)) ->
                      bind (rewrite x_t)
                        (fun uu___10_4131  ->
                           rewrite_all_context_equalities bs1)
                  | uu____4134 -> rewrite_all_context_equalities bs1))
let rewrite_eqs_from_context: Prims.unit tactic =
  bind cur_goal
    (fun g  ->
       match g with
       | (context,uu____4156) ->
           bind (binders_of_env context)
             (fun bs  -> rewrite_all_context_equalities bs))
let rewrite_equality: term tactic -> Prims.unit tactic =
  fun x  ->
    bind cur_goal
      (fun g  ->
         match g with
         | (context,uu____4200) ->
             bind x
               (fun t  ->
                  bind (binders_of_env context)
                    (fun bs  -> try_rewrite_equality t bs)))
let rewrite_all_equalities: Prims.unit tactic = visit simplify_eq_implication
let rec unfold_definition_and_simplify_eq':
  term -> Prims.unit -> (Prims.unit,Prims.unit) _dm4f_TAC_repr =
  fun tm  ->
    fun u  ->
      bind cur_goal
        (fun g  ->
           match g with
           | (uu____4308,goal_t) ->
               bind (term_as_formula goal_t)
                 (fun f  ->
                    match f with
                    | Some (App (hd,arg)) ->
                        bind (term_eq hd tm)
                          (fun b  -> if b then trivial else return ())
                    | uu____4335 ->
                        bind (destruct_equality_implication goal_t)
                          (fun r  ->
                             match r with
                             | None  -> fail "Not an equality implication"
                             | Some (uu____4357,rhs) ->
                                 bind implies_intro
                                   (fun eq_h  ->
                                      bind (rewrite eq_h)
                                        (fun uu___12_4374  ->
                                           bind clear
                                             (fun uu___11_4379  ->
                                                visit
                                                  (unfold_definition_and_simplify_eq'
                                                     tm))))))) ()
let unfold_definition_and_simplify_eq: term tactic -> Prims.unit tactic =
  fun tm  -> bind tm (fun tm'  -> unfold_definition_and_simplify_eq' tm')
type ('At,'Aa) by_tactic = 'Aa
let assert_by_tactic: Prims.unit tactic -> Prims.unit -> Prims.unit =
  fun t  -> fun p  -> ()
let liftM1' f ma = bind ma (fun a  -> f a)
let liftM1 f = liftM1' (fun x  -> return (f x))
let liftM2' f ma mb = bind ma (fun a  -> bind mb (fun b  -> f a b))
let liftM2 f = liftM2' (fun x  -> fun y  -> return (f x y))