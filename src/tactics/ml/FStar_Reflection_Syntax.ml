open Prims
type term = Prims.unit
type fv = Prims.unit
type binder = Prims.unit
type env = Prims.unit
type name = Prims.string Prims.list
type typ = term
type binders = binder Prims.list
type const =
  | C_Unit
  | C_Int of Prims.int
  | C_True
  | C_False
let uu___is_C_Unit: const -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Unit  -> true | uu____12 -> false
let uu___is_C_Int: const -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____20 -> false
let __proj__C_Int__item___0: const -> Prims.int =
  fun projectee  -> match projectee with | C_Int _0 -> _0
let uu___is_C_True: const -> Prims.bool =
  fun projectee  ->
    match projectee with | C_True  -> true | uu____36 -> false
let uu___is_C_False: const -> Prims.bool =
  fun projectee  ->
    match projectee with | C_False  -> true | uu____42 -> false
type term_view =
  | Tv_Var of binder
  | Tv_FVar of fv
  | Tv_App of term* term
  | Tv_Abs of binder* term
  | Tv_Arrow of binder* term
  | Tv_Type of Prims.unit
  | Tv_Refine of binder* term
  | Tv_Const of const
  | Tv_Unknown
let uu___is_Tv_Var: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Var _0 -> true | uu____98 -> false
let __proj__Tv_Var__item___0: term_view -> binder =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0
let uu___is_Tv_FVar: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____116 -> false
let __proj__Tv_FVar__item___0: term_view -> fv =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0
let uu___is_Tv_App: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_App (_0,_1) -> true | uu____136 -> false
let __proj__Tv_App__item___0: term_view -> term =
  fun projectee  -> match projectee with | Tv_App (_0,_1) -> _0
let __proj__Tv_App__item___1: term_view -> term =
  fun projectee  -> match projectee with | Tv_App (_0,_1) -> _1
let uu___is_Tv_Abs: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Abs (_0,_1) -> true | uu____170 -> false
let __proj__Tv_Abs__item___0: term_view -> binder =
  fun projectee  -> match projectee with | Tv_Abs (_0,_1) -> _0
let __proj__Tv_Abs__item___1: term_view -> term =
  fun projectee  -> match projectee with | Tv_Abs (_0,_1) -> _1
let uu___is_Tv_Arrow: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Arrow (_0,_1) -> true | uu____204 -> false
let __proj__Tv_Arrow__item___0: term_view -> binder =
  fun projectee  -> match projectee with | Tv_Arrow (_0,_1) -> _0
let __proj__Tv_Arrow__item___1: term_view -> term =
  fun projectee  -> match projectee with | Tv_Arrow (_0,_1) -> _1
let uu___is_Tv_Type: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____236 -> false
let __proj__Tv_Type__item___0: term_view -> Prims.unit = fun projectee  -> ()
let uu___is_Tv_Refine: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Refine (_0,_1) -> true | uu____256 -> false
let __proj__Tv_Refine__item___0: term_view -> binder =
  fun projectee  -> match projectee with | Tv_Refine (_0,_1) -> _0
let __proj__Tv_Refine__item___1: term_view -> term =
  fun projectee  -> match projectee with | Tv_Refine (_0,_1) -> _1
let uu___is_Tv_Const: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____288 -> false
let __proj__Tv_Const__item___0: term_view -> const =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0
let uu___is_Tv_Unknown: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Unknown  -> true | uu____304 -> false
let __type_of_binder: binder -> term =
  Obj.magic
    (fun uu____309  -> failwith "Not yet implemented:__type_of_binder")
let type_of_binder: binder -> term = fun b  -> __type_of_binder b
type ('Atv,'At) smaller = Obj.t
let __inspect: term -> term_view =
  Obj.magic (fun t  -> failwith "Not yet implemented:__inspect")
let inspect: term -> term_view = fun t  -> __inspect t
let __pack: term_view -> term =
  Obj.magic (fun uu____360  -> failwith "Not yet implemented:__pack")
let pack: term_view -> term = fun tv  -> __pack tv
let pack_inspect_inv: term -> Prims.unit =
  Obj.magic (fun t  -> failwith "Not yet implemented:pack_inspect_inv")
let inspect_pack_inv: term_view -> Prims.unit =
  Obj.magic (fun tv  -> failwith "Not yet implemented:inspect_pack_inv")
let __inspect_fv: fv -> name =
  Obj.magic (fun uu____379  -> failwith "Not yet implemented:__inspect_fv")
let inspect_fv: fv -> name = fun fv  -> __inspect_fv fv
let __pack_fv: name -> fv =
  Obj.magic (fun uu____388  -> failwith "Not yet implemented:__pack_fv")
let pack_fv: name -> fv = fun ns  -> __pack_fv ns
let __compare_binder: binder -> binder -> FStar_Order.order =
  Obj.magic
    (fun uu____401  ->
       fun uu____402  -> failwith "Not yet implemented:__compare_binder")
let compare_binder: binder -> binder -> FStar_Order.order =
  fun b1  -> fun b2  -> __compare_binder b1 b2
let __inspect_bv: binder -> Prims.string =
  Obj.magic (fun uu____415  -> failwith "Not yet implemented:__inspect_bv")
let inspect_bv: binder -> Prims.string = fun b  -> __inspect_bv b
let __binders_of_env: env -> binders =
  Obj.magic
    (fun uu____424  -> failwith "Not yet implemented:__binders_of_env")
let binders_of_env: env -> binders = fun e  -> __binders_of_env e
let __is_free: binder -> term -> Prims.bool =
  Obj.magic
    (fun uu____437  ->
       fun uu____438  -> failwith "Not yet implemented:__is_free")
let is_free: binder -> term -> Prims.bool = fun b  -> fun t  -> __is_free b t
let __term_eq: term -> term -> Prims.bool =
  Obj.magic
    (fun uu____455  ->
       fun uu____456  -> failwith "Not yet implemented:__term_eq")
let term_eq: term -> term -> Prims.bool =
  fun t1  -> fun t2  -> __term_eq t1 t2
let __term_to_string: term -> Prims.string =
  Obj.magic
    (fun uu____469  -> failwith "Not yet implemented:__term_to_string")
let term_to_string: term -> Prims.string = fun t  -> __term_to_string t
let __fresh_binder: typ -> binder =
  Obj.magic (fun uu____478  -> failwith "Not yet implemented:__fresh_binder")
let fresh_binder: typ -> binder = fun t  -> __fresh_binder t
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
let squash_qn: Prims.string Prims.list = ["Prims"; "squash"]
let int_lid: Prims.string Prims.list = ["Prims"; "int"]
let bool_lid: Prims.string Prims.list = ["Prims"; "bool"]
let unit_lid: Prims.string Prims.list = ["Prims"; "unit"]
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
let rec collect_app': term Prims.list -> term -> (term* term Prims.list) =
  fun args  ->
    fun t  ->
      match inspect t with
      | Tv_App (l,r) -> collect_app' (r :: args) l
      | uu____543 -> (t, args)
let collect_app: term -> (term* term Prims.list) = collect_app' []
let rec mk_app: term -> term Prims.list -> term =
  fun t  ->
    fun args  ->
      match args with | [] -> t | x::xs -> mk_app (pack (Tv_App (t, x))) xs
let rec eqlist f xs ys =
  match (xs, ys) with
  | ([],[]) -> true
  | (x::xs1,y::ys1) -> (f x y) && (eqlist f xs1 ys1)
  | uu____619 -> false
let fv_to_string: fv -> Prims.string =
  fun fv  -> FStar_String.concat "." (inspect_fv fv)
type norm_step =
  | Simpl
  | WHNF
  | Primops
  | Delta
let uu___is_Simpl: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____633 -> false
let uu___is_WHNF: norm_step -> Prims.bool =
  fun projectee  -> match projectee with | WHNF  -> true | uu____639 -> false
let uu___is_Primops: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____645 -> false
let uu___is_Delta: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____651 -> false
let compare_fv: fv -> fv -> FStar_Order.order =
  fun f1  ->
    fun f2  ->
      FStar_Order.compare_list
        (fun s1  ->
           fun s2  -> FStar_Order.order_from_int (FStar_String.compare s1 s2))
        (inspect_fv f1) (inspect_fv f2)
let rec compare_const: const -> const -> FStar_Order.order =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (C_Unit ,C_Unit ) -> FStar_Order.Eq
      | (C_Int i,C_Int j) -> FStar_Order.order_from_int (i - j)
      | (C_True ,C_True ) -> FStar_Order.Eq
      | (C_False ,C_False ) -> FStar_Order.Eq
      | (C_Unit ,uu____686) -> FStar_Order.Lt
      | (uu____687,C_Unit ) -> FStar_Order.Gt
      | (C_Int uu____688,uu____689) -> FStar_Order.Lt
      | (uu____690,C_Int uu____691) -> FStar_Order.Gt
      | (C_True ,uu____692) -> FStar_Order.Lt
      | (uu____693,C_True ) -> FStar_Order.Gt
      | (C_False ,uu____694) -> FStar_Order.Lt
      | (uu____695,C_False ) -> FStar_Order.Gt
let rec compare_term: term -> term -> FStar_Order.order =
  fun s  ->
    fun t  ->
      match ((inspect s), (inspect t)) with
      | (Tv_Var sv,Tv_Var tv) -> compare_binder sv tv
      | (Tv_FVar sv,Tv_FVar tv) -> compare_fv sv tv
      | (Tv_App (h1,a1),Tv_App (h2,a2)) ->
          FStar_Order.lex (compare_term h1 h2)
            (fun uu____778  -> compare_term a1 a2)
      | (Tv_Abs (b1,e1),Tv_Abs (b2,e2)) ->
          FStar_Order.lex (compare_binder b1 b2)
            (fun uu____783  -> compare_term e1 e2)
      | (Tv_Arrow (b1,e1),Tv_Arrow (b2,e2)) ->
          FStar_Order.lex (compare_binder b1 b2)
            (fun uu____788  -> compare_term e1 e2)
      | (Tv_Refine (b1,e1),Tv_Refine (b2,e2)) ->
          FStar_Order.lex (compare_binder b1 b2)
            (fun uu____793  -> compare_term e1 e2)
      | (Tv_Type (),Tv_Type ()) -> FStar_Order.Eq
      | (Tv_Const c1,Tv_Const c2) -> compare_const c1 c2
      | (Tv_Unknown ,Tv_Unknown ) -> FStar_Order.Eq
      | (Tv_Var uu____796,uu____797) -> FStar_Order.Lt
      | (uu____798,Tv_Var uu____799) -> FStar_Order.Gt
      | (Tv_FVar uu____800,uu____801) -> FStar_Order.Lt
      | (uu____802,Tv_FVar uu____803) -> FStar_Order.Gt
      | (Tv_App (uu____804,uu____805),uu____806) -> FStar_Order.Lt
      | (uu____807,Tv_App (uu____808,uu____809)) -> FStar_Order.Gt
      | (Tv_Abs (uu____810,uu____811),uu____812) -> FStar_Order.Lt
      | (uu____813,Tv_Abs (uu____814,uu____815)) -> FStar_Order.Gt
      | (Tv_Arrow (uu____816,uu____817),uu____818) -> FStar_Order.Lt
      | (uu____819,Tv_Arrow (uu____820,uu____821)) -> FStar_Order.Gt
      | (Tv_Type (),uu____822) -> FStar_Order.Lt
      | (uu____823,Tv_Type ()) -> FStar_Order.Gt
      | (Tv_Refine (uu____824,uu____825),uu____826) -> FStar_Order.Lt
      | (uu____827,Tv_Refine (uu____828,uu____829)) -> FStar_Order.Gt
      | (Tv_Const uu____830,uu____831) -> FStar_Order.Lt
      | (uu____832,Tv_Const uu____833) -> FStar_Order.Gt
      | (Tv_Unknown ,uu____834) -> FStar_Order.Lt
      | (uu____835,Tv_Unknown ) -> FStar_Order.Gt