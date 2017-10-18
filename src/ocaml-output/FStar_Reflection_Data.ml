open Prims
type name = Prims.string Prims.list[@@deriving show]
type typ = FStar_Syntax_Syntax.term[@@deriving show]
type binders = FStar_Syntax_Syntax.binder Prims.list[@@deriving show]
type vconst =
  | C_Unit 
  | C_Int of Prims.int 
  | C_True 
  | C_False 
  | C_String of Prims.string [@@deriving show]
let uu___is_C_Unit : vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Unit  -> true | uu____17 -> false
  
let uu___is_C_Int : vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____23 -> false
  
let __proj__C_Int__item___0 : vconst -> Prims.int =
  fun projectee  -> match projectee with | C_Int _0 -> _0 
let uu___is_C_True : vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_True  -> true | uu____36 -> false
  
let uu___is_C_False : vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_False  -> true | uu____41 -> false
  
let uu___is_C_String : vconst -> Prims.bool =
  fun projectee  ->
    match projectee with | C_String _0 -> true | uu____47 -> false
  
let __proj__C_String__item___0 : vconst -> Prims.string =
  fun projectee  -> match projectee with | C_String _0 -> _0 
type pattern =
  | Pat_Constant of vconst 
  | Pat_Cons of (FStar_Syntax_Syntax.fv,pattern Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Pat_Var of FStar_Syntax_Syntax.bv 
  | Pat_Wild of FStar_Syntax_Syntax.bv [@@deriving show]
let uu___is_Pat_Constant : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | Pat_Constant _0 -> true | uu____83 -> false
  
let __proj__Pat_Constant__item___0 : pattern -> vconst =
  fun projectee  -> match projectee with | Pat_Constant _0 -> _0 
let uu___is_Pat_Cons : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | Pat_Cons _0 -> true | uu____103 -> false
  
let __proj__Pat_Cons__item___0 :
  pattern ->
    (FStar_Syntax_Syntax.fv,pattern Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Pat_Cons _0 -> _0 
let uu___is_Pat_Var : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | Pat_Var _0 -> true | uu____135 -> false
  
let __proj__Pat_Var__item___0 : pattern -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Pat_Var _0 -> _0 
let uu___is_Pat_Wild : pattern -> Prims.bool =
  fun projectee  ->
    match projectee with | Pat_Wild _0 -> true | uu____149 -> false
  
let __proj__Pat_Wild__item___0 : pattern -> FStar_Syntax_Syntax.bv =
  fun projectee  -> match projectee with | Pat_Wild _0 -> _0 
type branch =
  (pattern,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2[@@deriving
                                                                    show]
type aqualv =
  | Q_Implicit 
  | Q_Explicit [@@deriving show]
let uu___is_Q_Implicit : aqualv -> Prims.bool =
  fun projectee  ->
    match projectee with | Q_Implicit  -> true | uu____166 -> false
  
let uu___is_Q_Explicit : aqualv -> Prims.bool =
  fun projectee  ->
    match projectee with | Q_Explicit  -> true | uu____171 -> false
  
type argv = (FStar_Syntax_Syntax.term,aqualv) FStar_Pervasives_Native.tuple2
[@@deriving show]
type term_view =
  | Tv_Var of FStar_Syntax_Syntax.binder 
  | Tv_FVar of FStar_Syntax_Syntax.fv 
  | Tv_App of (FStar_Syntax_Syntax.term,argv) FStar_Pervasives_Native.tuple2
  
  | Tv_Abs of (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | Tv_Arrow of (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
  FStar_Pervasives_Native.tuple2 
  | Tv_Type of Prims.unit 
  | Tv_Refine of (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | Tv_Const of vconst 
  | Tv_Uvar of (Prims.int,typ) FStar_Pervasives_Native.tuple2 
  | Tv_Let of
  (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple3 
  | Tv_Match of (FStar_Syntax_Syntax.term,branch Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Tv_Unknown [@@deriving show]
let uu___is_Tv_Var : term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Var _0 -> true | uu____257 -> false
  
let __proj__Tv_Var__item___0 : term_view -> FStar_Syntax_Syntax.binder =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0 
let uu___is_Tv_FVar : term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____271 -> false
  
let __proj__Tv_FVar__item___0 : term_view -> FStar_Syntax_Syntax.fv =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0 
let uu___is_Tv_App : term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_App _0 -> true | uu____289 -> false
  
let __proj__Tv_App__item___0 :
  term_view -> (FStar_Syntax_Syntax.term,argv) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tv_App _0 -> _0 
let uu___is_Tv_Abs : term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Abs _0 -> true | uu____319 -> false
  
let __proj__Tv_Abs__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tv_Abs _0 -> _0 
let uu___is_Tv_Arrow : term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Arrow _0 -> true | uu____349 -> false
  
let __proj__Tv_Arrow__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tv_Arrow _0 -> _0 
let uu___is_Tv_Type : term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____375 -> false
  
let __proj__Tv_Type__item___0 : term_view -> Prims.unit =
  fun projectee  -> () 
let uu___is_Tv_Refine : term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Refine _0 -> true | uu____393 -> false
  
let __proj__Tv_Refine__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tv_Refine _0 -> _0 
let uu___is_Tv_Const : term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____419 -> false
  
let __proj__Tv_Const__item___0 : term_view -> vconst =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0 
let uu___is_Tv_Uvar : term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Uvar _0 -> true | uu____437 -> false
  
let __proj__Tv_Uvar__item___0 :
  term_view -> (Prims.int,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Tv_Uvar _0 -> _0 
let uu___is_Tv_Let : term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Let _0 -> true | uu____469 -> false
  
let __proj__Tv_Let__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Tv_Let _0 -> _0 
let uu___is_Tv_Match : term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Match _0 -> true | uu____507 -> false
  
let __proj__Tv_Match__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.term,branch Prims.list)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Tv_Match _0 -> _0 
let uu___is_Tv_Unknown : term_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Tv_Unknown  -> true | uu____538 -> false
  
type comp_view =
  | C_Total of typ 
  | C_Lemma of (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C_Unknown [@@deriving show]
let uu___is_C_Total : comp_view -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Total _0 -> true | uu____556 -> false
  
let __proj__C_Total__item___0 : comp_view -> typ =
  fun projectee  -> match projectee with | C_Total _0 -> _0 
let uu___is_C_Lemma : comp_view -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Lemma _0 -> true | uu____574 -> false
  
let __proj__C_Lemma__item___0 :
  comp_view ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | C_Lemma _0 -> _0 
let uu___is_C_Unknown : comp_view -> Prims.bool =
  fun projectee  ->
    match projectee with | C_Unknown  -> true | uu____599 -> false
  
type ctor =
  | Ctor of (name,typ) FStar_Pervasives_Native.tuple2 [@@deriving show]
let uu___is_Ctor : ctor -> Prims.bool = fun projectee  -> true 
let __proj__Ctor__item___0 :
  ctor -> (name,typ) FStar_Pervasives_Native.tuple2 =
  fun projectee  -> match projectee with | Ctor _0 -> _0 
type sigelt_view =
  | Sg_Inductive of
  (name,FStar_Syntax_Syntax.binder Prims.list,typ,ctor Prims.list)
  FStar_Pervasives_Native.tuple4 
  | Sg_Let of (FStar_Syntax_Syntax.fv,typ,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple3 
  | Unk [@@deriving show]
let uu___is_Sg_Inductive : sigelt_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Sg_Inductive _0 -> true | uu____672 -> false
  
let __proj__Sg_Inductive__item___0 :
  sigelt_view ->
    (name,FStar_Syntax_Syntax.binder Prims.list,typ,ctor Prims.list)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Sg_Inductive _0 -> _0 
let uu___is_Sg_Let : sigelt_view -> Prims.bool =
  fun projectee  ->
    match projectee with | Sg_Let _0 -> true | uu____728 -> false
  
let __proj__Sg_Let__item___0 :
  sigelt_view ->
    (FStar_Syntax_Syntax.fv,typ,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple3
  = fun projectee  -> match projectee with | Sg_Let _0 -> _0 
let uu___is_Unk : sigelt_view -> Prims.bool =
  fun projectee  -> match projectee with | Unk  -> true | uu____759 -> false 
let fstar_refl_lid : Prims.string Prims.list -> FStar_Ident.lident =
  fun s  ->
    FStar_Ident.lid_of_path (FStar_List.append ["FStar"; "Reflection"] s)
      FStar_Range.dummyRange
  
let fstar_refl_basic_lid : Prims.string -> FStar_Ident.lident =
  fun s  -> fstar_refl_lid ["Basic"; s] 
let fstar_refl_types_lid : Prims.string -> FStar_Ident.lident =
  fun s  -> fstar_refl_lid ["Types"; s] 
let fstar_refl_syntax_lid : Prims.string -> FStar_Ident.lident =
  fun s  -> fstar_refl_lid ["Syntax"; s] 
let fstar_refl_data_lid : Prims.string -> FStar_Ident.lident =
  fun s  -> fstar_refl_lid ["Data"; s] 
let mk_refl_types_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____788 = fstar_refl_types_lid s  in
    FStar_Syntax_Syntax.tconst uu____788
  
let mk_refl_syntax_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____793 = fstar_refl_syntax_lid s  in
    FStar_Syntax_Syntax.tconst uu____793
  
let mk_refl_data_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____798 = fstar_refl_data_lid s  in
    FStar_Syntax_Syntax.tconst uu____798
  
let fstar_refl_tdataconstr :
  Prims.string Prims.list -> FStar_Syntax_Syntax.term =
  fun s  ->
    let uu____807 = fstar_refl_lid s  in
    FStar_Syntax_Syntax.tdataconstr uu____807
  
let fstar_refl_aqualv : FStar_Syntax_Syntax.term =
  mk_refl_data_lid_as_term "aqualv" 
let fstar_refl_env : FStar_Syntax_Syntax.term =
  mk_refl_types_lid_as_term "env" 
let fstar_refl_fvar : FStar_Syntax_Syntax.term =
  mk_refl_types_lid_as_term "fv" 
let fstar_refl_comp : FStar_Syntax_Syntax.term =
  mk_refl_types_lid_as_term "comp" 
let fstar_refl_comp_view : FStar_Syntax_Syntax.term =
  mk_refl_types_lid_as_term "comp_view" 
let fstar_refl_binder : FStar_Syntax_Syntax.term =
  mk_refl_types_lid_as_term "binder" 
let fstar_refl_binders : FStar_Syntax_Syntax.term =
  mk_refl_types_lid_as_term "binders" 
let fstar_refl_term_view : FStar_Syntax_Syntax.term =
  mk_refl_types_lid_as_term "term_view" 
let fstar_refl_sigelt : FStar_Syntax_Syntax.term =
  mk_refl_types_lid_as_term "sigelt" 
let fstar_refl_ctor : FStar_Syntax_Syntax.term =
  mk_refl_types_lid_as_term "ctor" 
let fstar_refl_pattern : FStar_Syntax_Syntax.term =
  mk_refl_syntax_lid_as_term "pattern" 
let fstar_refl_branch : FStar_Syntax_Syntax.term =
  mk_refl_types_lid_as_term "branch" 
let ref_Q_Explicit_lid : FStar_Ident.lident =
  fstar_refl_data_lid "Q_Explicit" 
let ref_Q_Implicit_lid : FStar_Ident.lident =
  fstar_refl_data_lid "Q_Implicit" 
let ref_Q_Explicit : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Q_Explicit_lid 
let ref_Q_Implicit : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Q_Implicit_lid 
let ref_C_Unit_lid : FStar_Ident.lident = fstar_refl_data_lid "C_Unit" 
let ref_C_True_lid : FStar_Ident.lident = fstar_refl_data_lid "C_True" 
let ref_C_False_lid : FStar_Ident.lident = fstar_refl_data_lid "C_False" 
let ref_C_Int_lid : FStar_Ident.lident = fstar_refl_data_lid "C_Int" 
let ref_C_String_lid : FStar_Ident.lident = fstar_refl_data_lid "C_String" 
let ref_C_Unit : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_C_Unit_lid 
let ref_C_True : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_C_True_lid 
let ref_C_False : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_C_False_lid 
let ref_C_Int : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_C_Int_lid 
let ref_C_String : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_C_String_lid 
let ref_Pat_Constant_lid : FStar_Ident.lident =
  fstar_refl_data_lid "Pat_Constant" 
let ref_Pat_Cons_lid : FStar_Ident.lident = fstar_refl_data_lid "Pat_Cons" 
let ref_Pat_Var_lid : FStar_Ident.lident = fstar_refl_data_lid "Pat_Var" 
let ref_Pat_Wild_lid : FStar_Ident.lident = fstar_refl_data_lid "Pat_Wild" 
let ref_Pat_Constant : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Pat_Constant_lid 
let ref_Pat_Cons : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Pat_Cons_lid 
let ref_Pat_Var : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Pat_Var_lid 
let ref_Pat_Wild : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Pat_Wild_lid 
let ref_Tv_Var_lid : FStar_Ident.lident = fstar_refl_data_lid "Tv_Var" 
let ref_Tv_FVar_lid : FStar_Ident.lident = fstar_refl_data_lid "Tv_FVar" 
let ref_Tv_App_lid : FStar_Ident.lident = fstar_refl_data_lid "Tv_App" 
let ref_Tv_Abs_lid : FStar_Ident.lident = fstar_refl_data_lid "Tv_Abs" 
let ref_Tv_Arrow_lid : FStar_Ident.lident = fstar_refl_data_lid "Tv_Arrow" 
let ref_Tv_Type_lid : FStar_Ident.lident = fstar_refl_data_lid "Tv_Type" 
let ref_Tv_Refine_lid : FStar_Ident.lident = fstar_refl_data_lid "Tv_Refine" 
let ref_Tv_Const_lid : FStar_Ident.lident = fstar_refl_data_lid "Tv_Const" 
let ref_Tv_Uvar_lid : FStar_Ident.lident = fstar_refl_data_lid "Tv_Uvar" 
let ref_Tv_Let_lid : FStar_Ident.lident = fstar_refl_data_lid "Tv_Let" 
let ref_Tv_Match_lid : FStar_Ident.lident = fstar_refl_data_lid "Tv_Match" 
let ref_Tv_Unknown_lid : FStar_Ident.lident =
  fstar_refl_data_lid "Tv_Unknown" 
let ref_Tv_Var : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Tv_Var_lid 
let ref_Tv_FVar : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Tv_FVar_lid 
let ref_Tv_App : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Tv_App_lid 
let ref_Tv_Abs : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Tv_Abs_lid 
let ref_Tv_Arrow : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Tv_Arrow_lid 
let ref_Tv_Type : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Tv_Type_lid 
let ref_Tv_Refine : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Tv_Refine_lid 
let ref_Tv_Const : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Tv_Const_lid 
let ref_Tv_Uvar : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Tv_Uvar_lid 
let ref_Tv_Let : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Tv_Let_lid 
let ref_Tv_Match : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Tv_Match_lid 
let ref_Tv_Unknown : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Tv_Unknown_lid 
let ref_C_Total_lid : FStar_Ident.lident = fstar_refl_data_lid "C_Total" 
let ref_C_Lemma_lid : FStar_Ident.lident = fstar_refl_data_lid "C_Lemma" 
let ref_C_Unknown_lid : FStar_Ident.lident = fstar_refl_data_lid "C_Unknown" 
let ref_C_Total : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_C_Total_lid 
let ref_C_Lemma : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_C_Lemma_lid 
let ref_C_Unknown : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_C_Unknown_lid 
let ref_Sg_Inductive_lid : FStar_Ident.lident =
  fstar_refl_data_lid "Sg_Inductive" 
let ref_Sg_Let_lid : FStar_Ident.lident = fstar_refl_data_lid "Sg_Let" 
let ref_Unk_lid : FStar_Ident.lident = fstar_refl_data_lid "Unk" 
let ref_Ctor_lid : FStar_Ident.lident = fstar_refl_data_lid "Ctor" 
let ref_Sg_Inductive : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Sg_Inductive_lid 
let ref_Sg_Let : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Sg_Let_lid 
let ref_Unk : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Unk_lid 
let ref_Ctor : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ref_Ctor_lid 
let t_binder : FStar_Syntax_Syntax.term =
  let uu____808 = fstar_refl_types_lid "binder"  in
  FStar_All.pipe_left FStar_Syntax_Syntax.tabbrev uu____808 
let t_term : FStar_Syntax_Syntax.term =
  let uu____809 = fstar_refl_types_lid "term"  in
  FStar_All.pipe_left FStar_Syntax_Syntax.tabbrev uu____809 
let t_fv : FStar_Syntax_Syntax.term =
  let uu____810 = fstar_refl_types_lid "fv"  in
  FStar_All.pipe_left FStar_Syntax_Syntax.tabbrev uu____810 
let t_binders : FStar_Syntax_Syntax.term =
  let uu____811 = fstar_refl_types_lid "binders"  in
  FStar_All.pipe_left FStar_Syntax_Syntax.tabbrev uu____811 
let ord_Lt_lid : FStar_Ident.lident =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Lt"] FStar_Range.dummyRange 
let ord_Eq_lid : FStar_Ident.lident =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Eq"] FStar_Range.dummyRange 
let ord_Gt_lid : FStar_Ident.lident =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Gt"] FStar_Range.dummyRange 
let ord_Lt : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ord_Lt_lid 
let ord_Eq : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ord_Eq_lid 
let ord_Gt : FStar_Syntax_Syntax.term =
  FStar_Syntax_Syntax.tdataconstr ord_Gt_lid 