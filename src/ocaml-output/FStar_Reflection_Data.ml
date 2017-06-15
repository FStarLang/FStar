open Prims
type vconst =
  | C_Unit
  | C_Int of Prims.string
  | C_True
  | C_False
let uu___is_C_Unit: vconst -> Prims.bool =
  fun projectee  -> match projectee with | C_Unit  -> true | uu____9 -> false
let uu___is_C_Int: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____15 -> false
let __proj__C_Int__item___0: vconst -> Prims.string =
  fun projectee  -> match projectee with | C_Int _0 -> _0
let uu___is_C_True: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_True  -> true | uu____28 -> false
let uu___is_C_False: vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_False  -> true | uu____33 -> false
type term_view =
  | Tv_Var of FStar_Syntax_Syntax.binder
  | Tv_FVar of FStar_Syntax_Syntax.fv
  | Tv_App of (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term)
  | Tv_Abs of (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term)
  | Tv_Arrow of (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term)
  | Tv_Type of Prims.unit
  | Tv_Refine of (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term)
  | Tv_Const of vconst
  | Tv_Unknown
let uu___is_Tv_Var: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Var _0 -> true | uu____79 -> false
let __proj__Tv_Var__item___0: term_view -> FStar_Syntax_Syntax.binder =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0
let uu___is_Tv_FVar: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____93 -> false
let __proj__Tv_FVar__item___0: term_view -> FStar_Syntax_Syntax.fv =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0
let uu___is_Tv_App: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_App _0 -> true | uu____109 -> false
let __proj__Tv_App__item___0:
  term_view -> (FStar_Syntax_Syntax.term* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_App _0 -> _0
let uu___is_Tv_Abs: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Abs _0 -> true | uu____131 -> false
let __proj__Tv_Abs__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Abs _0 -> _0
let uu___is_Tv_Arrow: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Arrow _0 -> true | uu____153 -> false
let __proj__Tv_Arrow__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Arrow _0 -> _0
let uu___is_Tv_Type: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____173 -> false
let __proj__Tv_Type__item___0: term_view -> Prims.unit = fun projectee  -> ()
let uu___is_Tv_Refine: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Refine _0 -> true | uu____189 -> false
let __proj__Tv_Refine__item___0:
  term_view -> (FStar_Syntax_Syntax.binder* FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Tv_Refine _0 -> _0
let uu___is_Tv_Const: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____209 -> false
let __proj__Tv_Const__item___0: term_view -> vconst =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0
let uu___is_Tv_Unknown: term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Unknown  -> true | uu____222 -> false
type norm_step =
  | Simpl
  | WHNF
  | Primops
  | Delta
let uu___is_Simpl: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Simpl  -> true | uu____227 -> false
let uu___is_WHNF: norm_step -> Prims.bool =
  fun projectee  -> match projectee with | WHNF  -> true | uu____232 -> false
let uu___is_Primops: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Primops  -> true | uu____237 -> false
let uu___is_Delta: norm_step -> Prims.bool =
  fun projectee  ->
    match projectee with | Delta  -> true | uu____242 -> false
let fstar_refl_lid: Prims.string Prims.list -> FStar_Ident.lident =
  fun s  ->
    FStar_Ident.lid_of_path (FStar_List.append ["FStar"; "Reflection"] s)
      FStar_Range.dummyRange
let lid_as_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____253 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None in
    FStar_All.pipe_right uu____253 FStar_Syntax_Syntax.fv_to_tm
let lid_as_data_tm: FStar_Ident.lident -> FStar_Syntax_Syntax.term =
  fun l  ->
    let uu____258 =
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        (Some FStar_Syntax_Syntax.Data_ctor) in
    FStar_Syntax_Syntax.fv_to_tm uu____258
let mk_refl_syntax_lid_as_term: Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____263 = fstar_refl_lid ["Syntax"; s] in lid_as_tm uu____263
let fstar_refl_lid_as_data_tm:
  Prims.string Prims.list -> FStar_Syntax_Syntax.term =
  fun s  -> let uu____270 = fstar_refl_lid s in lid_as_data_tm uu____270
let fstar_refl_term: FStar_Syntax_Syntax.term =
  mk_refl_syntax_lid_as_term "term"
let fstar_refl_env: FStar_Syntax_Syntax.term =
  mk_refl_syntax_lid_as_term "env"
let fstar_refl_fvar: FStar_Syntax_Syntax.term =
  mk_refl_syntax_lid_as_term "fv"
let fstar_refl_binder: FStar_Syntax_Syntax.term =
  mk_refl_syntax_lid_as_term "binder"
let fstar_refl_binders: FStar_Syntax_Syntax.term =
  mk_refl_syntax_lid_as_term "binders"
let fstar_refl_term_view: FStar_Syntax_Syntax.term =
  mk_refl_syntax_lid_as_term "term_view"
let fstar_refl_syntax_lid: Prims.string -> FStar_Ident.lident =
  fun s  -> fstar_refl_lid ["Syntax"; s]
let ref_Tv_Var_lid: FStar_Ident.lident = fstar_refl_syntax_lid "Tv_Var"
let ref_Tv_FVar_lid: FStar_Ident.lident = fstar_refl_syntax_lid "Tv_FVar"
let ref_Tv_App_lid: FStar_Ident.lident = fstar_refl_syntax_lid "Tv_App"
let ref_Tv_Abs_lid: FStar_Ident.lident = fstar_refl_syntax_lid "Tv_Abs"
let ref_Tv_Arrow_lid: FStar_Ident.lident = fstar_refl_syntax_lid "Tv_Arrow"
let ref_Tv_Type_lid: FStar_Ident.lident = fstar_refl_syntax_lid "Tv_Type"
let ref_Tv_Refine_lid: FStar_Ident.lident = fstar_refl_syntax_lid "Tv_Refine"
let ref_Tv_Const_lid: FStar_Ident.lident = fstar_refl_syntax_lid "Tv_Const"
let ref_Tv_Unknown_lid: FStar_Ident.lident =
  fstar_refl_syntax_lid "Tv_Unknown"
let ref_Tv_Var: FStar_Syntax_Syntax.term = lid_as_data_tm ref_Tv_Var_lid
let ref_Tv_FVar: FStar_Syntax_Syntax.term = lid_as_data_tm ref_Tv_FVar_lid
let ref_Tv_App: FStar_Syntax_Syntax.term = lid_as_data_tm ref_Tv_App_lid
let ref_Tv_Abs: FStar_Syntax_Syntax.term = lid_as_data_tm ref_Tv_Abs_lid
let ref_Tv_Arrow: FStar_Syntax_Syntax.term = lid_as_data_tm ref_Tv_Arrow_lid
let ref_Tv_Type: FStar_Syntax_Syntax.term = lid_as_data_tm ref_Tv_Type_lid
let ref_Tv_Refine: FStar_Syntax_Syntax.term =
  lid_as_data_tm ref_Tv_Refine_lid
let ref_Tv_Const: FStar_Syntax_Syntax.term = lid_as_data_tm ref_Tv_Const_lid
let ref_Tv_Unknown: FStar_Syntax_Syntax.term =
  lid_as_data_tm ref_Tv_Unknown_lid
let ref_C_Unit_lid: FStar_Ident.lident = fstar_refl_syntax_lid "C_Unit"
let ref_C_True_lid: FStar_Ident.lident = fstar_refl_syntax_lid "C_True"
let ref_C_False_lid: FStar_Ident.lident = fstar_refl_syntax_lid "C_False"
let ref_C_Int_lid: FStar_Ident.lident = fstar_refl_syntax_lid "C_Int"
let ref_C_Unit: FStar_Syntax_Syntax.term = lid_as_data_tm ref_C_Unit_lid
let ref_C_True: FStar_Syntax_Syntax.term = lid_as_data_tm ref_C_True_lid
let ref_C_False: FStar_Syntax_Syntax.term = lid_as_data_tm ref_C_False_lid
let ref_C_Int: FStar_Syntax_Syntax.term = lid_as_data_tm ref_C_Int_lid
type order =
  | Lt
  | Eq
  | Gt
let uu___is_Lt: order -> Prims.bool =
  fun projectee  -> match projectee with | Lt  -> true | uu____279 -> false
let uu___is_Eq: order -> Prims.bool =
  fun projectee  -> match projectee with | Eq  -> true | uu____284 -> false
let uu___is_Gt: order -> Prims.bool =
  fun projectee  -> match projectee with | Gt  -> true | uu____289 -> false
let ord_Lt_lid: FStar_Ident.lident =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Lt"] FStar_Range.dummyRange
let ord_Eq_lid: FStar_Ident.lident =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Eq"] FStar_Range.dummyRange
let ord_Gt_lid: FStar_Ident.lident =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Gt"] FStar_Range.dummyRange
let ord_Lt: FStar_Syntax_Syntax.term = lid_as_data_tm ord_Lt_lid
let ord_Eq: FStar_Syntax_Syntax.term = lid_as_data_tm ord_Eq_lid
let ord_Gt: FStar_Syntax_Syntax.term = lid_as_data_tm ord_Gt_lid
let fstar_refl_norm_step: FStar_Syntax_Syntax.term =
  mk_refl_syntax_lid_as_term "norm_step"
let ref_Simpl_lid: FStar_Ident.lident = fstar_refl_syntax_lid "Simpl"
let ref_WHNF_lid: FStar_Ident.lident = fstar_refl_syntax_lid "WHNF"
let ref_Primops_lid: FStar_Ident.lident = fstar_refl_syntax_lid "Primops"
let ref_Delta_lid: FStar_Ident.lident = fstar_refl_syntax_lid "Delta"
let ref_Simpl: FStar_Syntax_Syntax.term = lid_as_data_tm ref_Simpl_lid
let ref_WHNF: FStar_Syntax_Syntax.term = lid_as_data_tm ref_WHNF_lid
let ref_Primops: FStar_Syntax_Syntax.term = lid_as_data_tm ref_Primops_lid
let ref_Delta: FStar_Syntax_Syntax.term = lid_as_data_tm ref_Delta_lid