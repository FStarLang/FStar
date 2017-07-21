open Prims
type name = Prims.string Prims.list
type typ = FStar_Reflection_Types.term
type binders = FStar_Reflection_Types.binder Prims.list
type const = FStar_Reflection_Data.vconst
  (* | C_Unit *)
  (* | C_Int of Prims.int *)
  (* | C_True *)
  (* | C_False *)
let uu___is_C_Unit: const -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Unit  -> true | uu____13 -> false
let uu___is_C_Int: const -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____22 -> false
let __proj__C_Int__item___0: const -> Prims.int =
  fun projectee  -> match projectee with | C_Int _0 -> _0
let uu___is_C_True: const -> Prims.bool =
  fun projectee  ->
    match projectee with | C_True  -> true | uu____40 -> false
let uu___is_C_False: const -> Prims.bool =
  fun projectee  ->
    match projectee with | C_False  -> true | uu____47 -> false
type term_view = FStar_Reflection_Data.term_view
  (* | Tv_Var of FStar_Reflection_Types.binder *)
  (* | Tv_FVar of FStar_Reflection_Types.fv *)
  (* | Tv_App of FStar_Reflection_Types.term* FStar_Reflection_Types.term *)
  (* | Tv_Abs of FStar_Reflection_Types.binder* FStar_Reflection_Types.term *)
  (* | Tv_Arrow of FStar_Reflection_Types.binder* FStar_Reflection_Types.term *)
  (* | Tv_Type of Prims.unit *)
  (* | Tv_Refine of FStar_Reflection_Types.binder* FStar_Reflection_Types.term *)
  (* | Tv_Const of const *)
  (* | Tv_Unknown *)
let uu___is_Tv_Var: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Var _0 -> true | uu____104 -> false
let __proj__Tv_Var__item___0: term_view -> FStar_Reflection_Types.binder =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0
let uu___is_Tv_FVar: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____124 -> false
let __proj__Tv_FVar__item___0: term_view -> FStar_Reflection_Types.fv =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0
let uu___is_Tv_App: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_App (_0,_1) -> true | uu____146 -> false
let __proj__Tv_App__item___0: term_view -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Tv_App (_0,_1) -> _0
let __proj__Tv_App__item___1: term_view -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Tv_App (_0,_1) -> _1
let uu___is_Tv_Abs: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Abs (_0,_1) -> true | uu____183 -> false
let __proj__Tv_Abs__item___0: term_view -> FStar_Reflection_Types.binder =
  fun projectee  -> match projectee with | Tv_Abs (_0,_1) -> _0
let __proj__Tv_Abs__item___1: term_view -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Tv_Abs (_0,_1) -> _1
let uu___is_Tv_Arrow: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Arrow (_0,_1) -> true | uu____220 -> false
let __proj__Tv_Arrow__item___0: term_view -> FStar_Reflection_Types.binder =
  fun projectee  -> match projectee with | Tv_Arrow (_0,_1) -> _0
let __proj__Tv_Arrow__item___1: term_view -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Tv_Arrow (_0,_1) -> _1
let uu___is_Tv_Type: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____255 -> false
let __proj__Tv_Type__item___0: term_view -> Prims.unit = fun projectee  -> ()
let uu___is_Tv_Refine: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Refine (_0,_1) -> true | uu____277 -> false
let __proj__Tv_Refine__item___0: term_view -> FStar_Reflection_Types.binder =
  fun projectee  -> match projectee with | Tv_Refine (_0,_1) -> _0
let __proj__Tv_Refine__item___1: term_view -> FStar_Reflection_Types.term =
  fun projectee  -> match projectee with | Tv_Refine (_0,_1) -> _1
let uu___is_Tv_Const: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____312 -> false
let __proj__Tv_Const__item___0: term_view -> const =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0
let uu___is_Tv_Unknown: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Unknown  -> true | uu____330 -> false
let __type_of_binder:
  FStar_Reflection_Types.binder -> FStar_Reflection_Types.term =
  Obj.magic
    (fun uu____336  -> failwith "Not yet implemented:__type_of_binder")
let type_of_binder:
  FStar_Reflection_Types.binder -> FStar_Reflection_Types.term =
  fun b  -> __type_of_binder b
type ('Atv,'At) smaller = Obj.t
let __inspect: FStar_Reflection_Types.term -> term_view =
    FStar_Reflection_Basic.inspect
let inspect: FStar_Reflection_Types.term -> term_view = fun t  -> __inspect t
let __pack: term_view -> FStar_Reflection_Types.term =
    FStar_Reflection_Basic.pack
let pack: term_view -> FStar_Reflection_Types.term = fun tv  -> __pack tv
let pack_inspect_inv: FStar_Reflection_Types.term -> Prims.unit =
  Obj.magic (fun t  -> failwith "Not yet implemented:pack_inspect_inv")
let inspect_pack_inv: term_view -> Prims.unit =
  Obj.magic (fun tv  -> failwith "Not yet implemented:inspect_pack_inv")
let __inspect_fv: FStar_Reflection_Types.fv -> name =
    FStar_Reflection_Basic.inspect_fv
let inspect_fv: FStar_Reflection_Types.fv -> name =
  fun fv  -> __inspect_fv fv
let __pack_fv: name -> FStar_Reflection_Types.fv =
    FStar_Reflection_Basic.pack_fv
let pack_fv: name -> FStar_Reflection_Types.fv = fun ns  -> __pack_fv ns
let __compare_binder:
  FStar_Reflection_Types.binder ->
    FStar_Reflection_Types.binder -> FStar_Order.order
  =
      fun b1 b2 -> match FStar_Reflection_Basic.order_binder b1 b2
      with
      | FStar_Reflection_Data.Eq -> FStar_Order.Eq
      | FStar_Reflection_Data.Lt -> FStar_Order.Lt
      | FStar_Reflection_Data.Gt -> FStar_Order.Gt
let compare_binder:
  FStar_Reflection_Types.binder ->
    FStar_Reflection_Types.binder -> FStar_Order.order
  = fun b1  -> fun b2  -> __compare_binder b1 b2
let __inspect_bv: FStar_Reflection_Types.binder -> Prims.string =
  Obj.magic (fun uu____458  -> failwith "Not yet implemented:__inspect_bv")
let inspect_bv: FStar_Reflection_Types.binder -> Prims.string =
  fun b  -> __inspect_bv b
let __binders_of_env: FStar_Reflection_Types.env -> binders =
  Obj.magic
    (fun uu____469  -> failwith "Not yet implemented:__binders_of_env")
let binders_of_env: FStar_Reflection_Types.env -> binders =
  fun e  -> __binders_of_env e
let __is_free:
  FStar_Reflection_Types.binder -> FStar_Reflection_Types.term -> Prims.bool
  =
  Obj.magic
    (fun uu____485  ->
       fun uu____486  -> failwith "Not yet implemented:__is_free")
let is_free:
  FStar_Reflection_Types.binder -> FStar_Reflection_Types.term -> Prims.bool
  = fun b  -> fun t  -> __is_free b t
let __term_eq:
  FStar_Reflection_Types.term -> FStar_Reflection_Types.term -> Prims.bool =
      FStar_Syntax_Util.term_eq
let term_eq:
  FStar_Reflection_Types.term -> FStar_Reflection_Types.term -> Prims.bool =
  fun t1  -> fun t2  -> __term_eq t1 t2
let __term_to_string: FStar_Reflection_Types.term -> Prims.string =
    FStar_Syntax_Print.term_to_string
let term_to_string: FStar_Reflection_Types.term -> Prims.string =
  fun t  -> __term_to_string t
let __fresh_binder: typ -> FStar_Reflection_Types.binder =
  (fun t -> (FStar_Syntax_Syntax.gen_bv "__refl" None t, None))
let fresh_binder: typ -> FStar_Reflection_Types.binder =
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
let exists_qn: Prims.string Prims.list = ["Prims"; "l_Exists"]
let squash_qn: Prims.string Prims.list = ["Prims"; "squash"]
let bool_true_qn: Prims.string Prims.list = ["Prims"; "true"]
let bool_false_qn: Prims.string Prims.list = ["Prims"; "false"]
let int_lid: Prims.string Prims.list = ["Prims"; "int"]
let bool_lid: Prims.string Prims.list = ["Prims"; "bool"]
let unit_lid: Prims.string Prims.list = ["Prims"; "unit"]
let add_qn: Prims.string Prims.list = ["Prims"; "op_Addition"]
let neg_qn: Prims.string Prims.list = ["Prims"; "op_Minus"]
let minus_qn: Prims.string Prims.list = ["Prims"; "op_Subtraction"]
let mult_qn: Prims.string Prims.list = ["Prims"; "op_Multiply"]
let mult'_qn: Prims.string Prims.list = ["FStar"; "Mul"; "op_Star"]
let div_qn: Prims.string Prims.list = ["Prims"; "op_Division"]
let lt_qn: Prims.string Prims.list = ["Prims"; "op_LessThan"]
let lte_qn: Prims.string Prims.list = ["Prims"; "op_LessThanOrEqual"]
let gt_qn: Prims.string Prims.list = ["Prims"; "op_GreaterThan"]
let gte_qn: Prims.string Prims.list = ["Prims"; "op_GreaterThanOrEqual"]
let mod_qn: Prims.string Prims.list = ["Prims"; "op_Modulus"]
let rec collect_app':
  FStar_Reflection_Types.term Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term* FStar_Reflection_Types.term Prims.list)
  =
  fun args  ->
    fun t  ->
      match inspect t with
      | Tv_App (l,r) -> collect_app' (r :: args) l
      | uu____608 -> (t, args)
let collect_app:
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term* FStar_Reflection_Types.term Prims.list)
  = collect_app' []
let rec mk_app:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list -> FStar_Reflection_Types.term
  =
  fun t  ->
    fun args  ->
      match args with | [] -> t | x::xs -> mk_app (pack (Tv_App (t, x))) xs
let rec eqlist f xs ys =
  match (xs, ys) with
  | ([],[]) -> true
  | (x::xs1,y::ys1) -> (f x y) && (eqlist f xs1 ys1)
  | uu____691 -> false
let fv_to_string: FStar_Reflection_Types.fv -> Prims.string =
  fun fv  -> FStar_String.concat "." (inspect_fv fv)
type norm_step =
  | Simpl
  | WHNF
  | Primops
  | Delta
let uu___is_Simpl: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____707 -> false
let uu___is_WHNF: norm_step -> Prims.bool =
  fun projectee  -> match projectee with | WHNF  -> true | uu____714 -> false
let uu___is_Primops: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____721 -> false
let uu___is_Delta: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____728 -> false
let compare_fv:
  FStar_Reflection_Types.fv -> FStar_Reflection_Types.fv -> FStar_Order.order
  =
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
      | (C_Unit ,uu____767) -> FStar_Order.Lt
      | (uu____768,C_Unit ) -> FStar_Order.Gt
      | (C_Int uu____769,uu____770) -> FStar_Order.Lt
      | (uu____771,C_Int uu____772) -> FStar_Order.Gt
      | (C_True ,uu____773) -> FStar_Order.Lt
      | (uu____774,C_True ) -> FStar_Order.Gt
      | (C_False ,uu____775) -> FStar_Order.Lt
      | (uu____776,C_False ) -> FStar_Order.Gt
let rec compare_term:
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term -> FStar_Order.order
  =
  fun s  ->
    fun t  ->
      match ((inspect s), (inspect t)) with
      | (Tv_Var sv,Tv_Var tv) -> compare_binder sv tv
      | (Tv_FVar sv,Tv_FVar tv) -> compare_fv sv tv
      | (Tv_App (h1,a1),Tv_App (h2,a2)) ->
          FStar_Order.lex (compare_term h1 h2)
            (fun uu____861  -> compare_term a1 a2)
      | (Tv_Abs (b1,e1),Tv_Abs (b2,e2)) ->
          FStar_Order.lex (compare_binder b1 b2)
            (fun uu____866  -> compare_term e1 e2)
      | (Tv_Arrow (b1,e1),Tv_Arrow (b2,e2)) ->
          FStar_Order.lex (compare_binder b1 b2)
            (fun uu____871  -> compare_term e1 e2)
      | (Tv_Refine (b1,e1),Tv_Refine (b2,e2)) ->
          FStar_Order.lex (compare_binder b1 b2)
            (fun uu____876  -> compare_term e1 e2)
      | (Tv_Type (),Tv_Type ()) -> FStar_Order.Eq
      | (Tv_Const c1,Tv_Const c2) -> compare_const c1 c2
      | (Tv_Unknown ,Tv_Unknown ) -> FStar_Order.Eq
      | (Tv_Var uu____879,uu____880) -> FStar_Order.Lt
      | (uu____881,Tv_Var uu____882) -> FStar_Order.Gt
      | (Tv_FVar uu____883,uu____884) -> FStar_Order.Lt
      | (uu____885,Tv_FVar uu____886) -> FStar_Order.Gt
      | (Tv_App (uu____887,uu____888),uu____889) -> FStar_Order.Lt
      | (uu____890,Tv_App (uu____891,uu____892)) -> FStar_Order.Gt
      | (Tv_Abs (uu____893,uu____894),uu____895) -> FStar_Order.Lt
      | (uu____896,Tv_Abs (uu____897,uu____898)) -> FStar_Order.Gt
      | (Tv_Arrow (uu____899,uu____900),uu____901) -> FStar_Order.Lt
      | (uu____902,Tv_Arrow (uu____903,uu____904)) -> FStar_Order.Gt
      | (Tv_Type (),uu____905) -> FStar_Order.Lt
      | (uu____906,Tv_Type ()) -> FStar_Order.Gt
      | (Tv_Refine (uu____907,uu____908),uu____909) -> FStar_Order.Lt
      | (uu____910,Tv_Refine (uu____911,uu____912)) -> FStar_Order.Gt
      | (Tv_Const uu____913,uu____914) -> FStar_Order.Lt
      | (uu____915,Tv_Const uu____916) -> FStar_Order.Gt
      | (Tv_Unknown ,uu____917) -> FStar_Order.Lt
      | (uu____918,Tv_Unknown ) -> FStar_Order.Gt