open Prims
type bv = Prims.unit
type name = Prims.string Prims.list
type typ = FStar_Tactics_Types.term
type binders = FStar_Tactics_Types.binder Prims.list
type const =
  | C_Unit
  | C_Int of Prims.int
let uu___is_C_Unit: const -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Unit  -> true | uu____11 -> false
let uu___is_C_Int: const -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____19 -> false
let __proj__C_Int__item___0: const -> Prims.int =
  fun projectee  -> match projectee with | C_Int _0 -> _0
type term_view =
  | Tv_Var of FStar_Tactics_Types.binder
  | Tv_FVar of FStar_Tactics_Types.fv
  | Tv_App of FStar_Tactics_Types.term* FStar_Tactics_Types.term
  | Tv_Abs of FStar_Tactics_Types.binder* FStar_Tactics_Types.term
  | Tv_Arrow of FStar_Tactics_Types.binder* FStar_Tactics_Types.term
  | Tv_Type of Prims.unit
  | Tv_Refine of FStar_Tactics_Types.binder* FStar_Tactics_Types.term
  | Tv_Const of const
  | Tv_Unknown
let uu___is_Tv_Var: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Var _0 -> true | uu____73 -> false
let __proj__Tv_Var__item___0: term_view -> FStar_Tactics_Types.binder =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0
let uu___is_Tv_FVar: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____91 -> false
let __proj__Tv_FVar__item___0: term_view -> FStar_Tactics_Types.fv =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0
let uu___is_Tv_App: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_App (_0,_1) -> true | uu____111 -> false
let __proj__Tv_App__item___0: term_view -> FStar_Tactics_Types.term =
  fun projectee  -> match projectee with | Tv_App (_0,_1) -> _0
let __proj__Tv_App__item___1: term_view -> FStar_Tactics_Types.term =
  fun projectee  -> match projectee with | Tv_App (_0,_1) -> _1
let uu___is_Tv_Abs: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Abs (_0,_1) -> true | uu____145 -> false
let __proj__Tv_Abs__item___0: term_view -> FStar_Tactics_Types.binder =
  fun projectee  -> match projectee with | Tv_Abs (_0,_1) -> _0
let __proj__Tv_Abs__item___1: term_view -> FStar_Tactics_Types.term =
  fun projectee  -> match projectee with | Tv_Abs (_0,_1) -> _1
let uu___is_Tv_Arrow: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Arrow (_0,_1) -> true | uu____179 -> false
let __proj__Tv_Arrow__item___0: term_view -> FStar_Tactics_Types.binder =
  fun projectee  -> match projectee with | Tv_Arrow (_0,_1) -> _0
let __proj__Tv_Arrow__item___1: term_view -> FStar_Tactics_Types.term =
  fun projectee  -> match projectee with | Tv_Arrow (_0,_1) -> _1
let uu___is_Tv_Type: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____211 -> false
let __proj__Tv_Type__item___0: term_view -> Prims.unit = fun projectee  -> ()
let uu___is_Tv_Refine: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Refine (_0,_1) -> true | uu____231 -> false
let __proj__Tv_Refine__item___0: term_view -> FStar_Tactics_Types.binder =
  fun projectee  -> match projectee with | Tv_Refine (_0,_1) -> _0
let __proj__Tv_Refine__item___1: term_view -> FStar_Tactics_Types.term =
  fun projectee  -> match projectee with | Tv_Refine (_0,_1) -> _1
let uu___is_Tv_Const: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____263 -> false
let __proj__Tv_Const__item___0: term_view -> const =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0
let uu___is_Tv_Unknown: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Unknown  -> true | uu____279 -> false
let __type_of_binder: FStar_Tactics_Types.binder -> FStar_Tactics_Types.term
  =
  Obj.magic
    (fun uu____284  -> failwith "Not yet implemented:__type_of_binder")
let type_of_binder: FStar_Tactics_Types.binder -> FStar_Tactics_Types.term =
  fun b  -> __type_of_binder b
type ('Atv,'At) smaller = Obj.t
let __inspect: FStar_Tactics_Types.term -> term_view =
  Obj.magic (fun t  -> failwith "Not yet implemented:__inspect")
let inspect: FStar_Tactics_Types.term -> term_view = fun t  -> __inspect t
let __pack: term_view -> FStar_Tactics_Types.term =
  Obj.magic (fun uu____327  -> failwith "Not yet implemented:__pack")
let pack: term_view -> FStar_Tactics_Types.term = fun tv  -> __pack tv
let pack_inspect_inv: FStar_Tactics_Types.term -> Prims.unit =
  Obj.magic (fun t  -> failwith "Not yet implemented:pack_inspect_inv")
let inspect_pack_inv: term_view -> Prims.unit =
  Obj.magic (fun tv  -> failwith "Not yet implemented:inspect_pack_inv")
let __inspect_fv: FStar_Tactics_Types.fv -> name =
  Obj.magic (fun uu____346  -> failwith "Not yet implemented:__inspect_fv")
let inspect_fv: FStar_Tactics_Types.fv -> name = fun fv  -> __inspect_fv fv
let __pack_fv: name -> FStar_Tactics_Types.fv =
  Obj.magic (fun uu____355  -> failwith "Not yet implemented:__pack_fv")
let pack_fv: name -> FStar_Tactics_Types.fv = fun ns  -> __pack_fv ns
let __compare_binder:
  FStar_Tactics_Types.binder ->
    FStar_Tactics_Types.binder -> FStar_Order.order
  =
  Obj.magic
    (fun uu____368  ->
       fun uu____369  -> failwith "Not yet implemented:__compare_binder")
let compare_binder:
  FStar_Tactics_Types.binder ->
    FStar_Tactics_Types.binder -> FStar_Order.order
  = fun b1  -> fun b2  -> __compare_binder b1 b2
let __inspect_bv: FStar_Tactics_Types.binder -> Prims.string =
  Obj.magic (fun uu____382  -> failwith "Not yet implemented:__inspect_bv")
let inspect_bv: FStar_Tactics_Types.binder -> Prims.string =
  fun b  -> __inspect_bv b
let __binders_of_env: FStar_Tactics_Types.env -> binders =
  Obj.magic
    (fun uu____391  -> failwith "Not yet implemented:__binders_of_env")
let binders_of_env: FStar_Tactics_Types.env -> binders =
  fun e  -> __binders_of_env e
let __is_free:
  FStar_Tactics_Types.binder -> FStar_Tactics_Types.term -> Prims.bool =
  Obj.magic
    (fun uu____404  ->
       fun uu____405  -> failwith "Not yet implemented:__is_free")
let is_free:
  FStar_Tactics_Types.binder -> FStar_Tactics_Types.term -> Prims.bool =
  fun b  -> fun t  -> __is_free b t
let __term_eq:
  FStar_Tactics_Types.term -> FStar_Tactics_Types.term -> Prims.bool =
  Obj.magic
    (fun uu____422  ->
       fun uu____423  -> failwith "Not yet implemented:__term_eq")
let term_eq:
  FStar_Tactics_Types.term -> FStar_Tactics_Types.term -> Prims.bool =
  fun t1  -> fun t2  -> __term_eq t1 t2
let __term_to_string: FStar_Tactics_Types.term -> Prims.string =
  Obj.magic
    (fun uu____436  -> failwith "Not yet implemented:__term_to_string")
let term_to_string: FStar_Tactics_Types.term -> Prims.string =
  fun t  -> __term_to_string t
let __fresh_binder: typ -> FStar_Tactics_Types.binder =
  Obj.magic (fun uu____445  -> failwith "Not yet implemented:__fresh_binder")
let fresh_binder: typ -> FStar_Tactics_Types.binder =
  fun t  -> __fresh_binder t
let rec flatten_name: name -> Prims.string =
  fun ns  ->
    match ns with
    | [] -> ""
    | n::[] -> n
    | n::ns1 -> Prims.strcat n (Prims.strcat "." (flatten_name ns1))
let imp_qn: Prims.string Prims.list = ["Prims"; "l_imp"]
let and_qn: Prims.string Prims.list = ["Prims"; "l_and"]
let or_qn: Prims.string Prims.list = ["Prims"; "l_or"]
let not_qn: Prims.string Prims.list = ["Prims"; "l_not"]
let iff_qn: Prims.string Prims.list = ["Prims"; "l_iff"]
let eq2_qn: Prims.string Prims.list = ["Prims"; "eq2"]
let eq1_qn: Prims.string Prims.list = ["Prims"; "eq"]
let true_qn: Prims.string Prims.list = ["Prims"; "l_True"]
let false_qn: Prims.string Prims.list = ["Prims"; "l_False"]
let b2t_qn: Prims.string Prims.list = ["Prims"; "b2t"]
let forall_qn: Prims.string Prims.list = ["Prims"; "l_Forall"]
let add_qn: Prims.string Prims.list = ["Prims"; "op_Addition"]
let neg_qn: Prims.string Prims.list = ["Prims"; "op_Minus"]
let minus_qn: Prims.string Prims.list = ["Prims"; "op_Subtraction"]
let mult_qn: Prims.string Prims.list = ["Prims"; "op_Multiply"]
let div_qn: Prims.string Prims.list = ["Prims"; "op_Division"]
let lt_qn: Prims.string Prims.list = ["Prims"; "op_LessThan"]
let lte_qn: Prims.string Prims.list = ["Prims"; "op_LessThanOrEqual"]
let gt_qn: Prims.string Prims.list = ["Prims"; "op_GreaterThan"]
let gte_qn: Prims.string Prims.list = ["Prims"; "op_GreaterThanOrEqual"]
let mod_qn: Prims.string Prims.list = ["Prims"; "op_Modulus"]
let rec collect_app':
  FStar_Tactics_Types.term Prims.list ->
    FStar_Tactics_Types.term ->
      (FStar_Tactics_Types.term* FStar_Tactics_Types.term Prims.list)
  =
  fun args  ->
    fun t  ->
      match inspect t with
      | Tv_App (l,r) -> collect_app' (r :: args) l
      | uu____506 -> (t, args)
let collect_app:
  FStar_Tactics_Types.term ->
    (FStar_Tactics_Types.term* FStar_Tactics_Types.term Prims.list)
  = collect_app' []
let rec mk_app:
  FStar_Tactics_Types.term ->
    FStar_Tactics_Types.term Prims.list -> FStar_Tactics_Types.term
  =
  fun t  ->
    fun args  ->
      match args with | [] -> t | x::xs -> mk_app (pack (Tv_App (t, x))) xs
let rec eqlist f xs ys =
  match (xs, ys) with
  | ([],[]) -> true
  | (x::xs1,y::ys1) -> (f x y) && (eqlist f xs1 ys1)
  | uu____582 -> false
let eq_qn: Prims.string Prims.list -> Prims.string Prims.list -> Prims.bool =
  eqlist
    (fun s1  ->
       fun s2  -> (FStar_String.compare s1 s2) = (Prims.parse_int "0"))
let fv_to_string: FStar_Tactics_Types.fv -> Prims.string =
  fun fv  -> FStar_String.concat "." (inspect_fv fv)