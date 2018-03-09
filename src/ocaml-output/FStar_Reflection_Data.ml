open Prims
type name = Prims.string Prims.list[@@deriving show]
type typ = FStar_Syntax_Syntax.term[@@deriving show]
type binders = FStar_Syntax_Syntax.binder Prims.list[@@deriving show]
type vconst =
  | C_Unit 
  | C_Int of FStar_BigInt.t 
  | C_True 
  | C_False 
  | C_String of Prims.string [@@deriving show]
let (uu___is_C_Unit : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Unit  -> true | uu____16 -> false
  
let (uu___is_C_Int : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____21 -> false
  
let (__proj__C_Int__item___0 : vconst -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | C_Int _0 -> _0 
let (uu___is_C_True : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_True  -> true | uu____32 -> false
  
let (uu___is_C_False : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_False  -> true | uu____36 -> false
  
let (uu___is_C_String : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_String _0 -> true | uu____41 -> false
  
let (__proj__C_String__item___0 : vconst -> Prims.string) =
  fun projectee  -> match projectee with | C_String _0 -> _0 
type pattern =
  | Pat_Constant of vconst 
  | Pat_Cons of (FStar_Syntax_Syntax.fv,pattern Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Pat_Var of FStar_Syntax_Syntax.binder 
  | Pat_Wild of FStar_Syntax_Syntax.binder [@@deriving show]
let (uu___is_Pat_Constant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_Constant _0 -> true | uu____75 -> false
  
let (__proj__Pat_Constant__item___0 : pattern -> vconst) =
  fun projectee  -> match projectee with | Pat_Constant _0 -> _0 
let (uu___is_Pat_Cons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_Cons _0 -> true | uu____93 -> false
  
let (__proj__Pat_Cons__item___0 :
  pattern ->
    (FStar_Syntax_Syntax.fv,pattern Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Pat_Cons _0 -> _0 
let (uu___is_Pat_Var : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_Var _0 -> true | uu____123 -> false
  
let (__proj__Pat_Var__item___0 : pattern -> FStar_Syntax_Syntax.binder) =
  fun projectee  -> match projectee with | Pat_Var _0 -> _0 
let (uu___is_Pat_Wild : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_Wild _0 -> true | uu____135 -> false
  
let (__proj__Pat_Wild__item___0 : pattern -> FStar_Syntax_Syntax.binder) =
  fun projectee  -> match projectee with | Pat_Wild _0 -> _0 
type branch =
  (pattern,FStar_Syntax_Syntax.term) FStar_Pervasives_Native.tuple2[@@deriving
                                                                    show]
type aqualv =
  | Q_Implicit 
  | Q_Explicit [@@deriving show]
let (uu___is_Q_Implicit : aqualv -> Prims.bool) =
  fun projectee  ->
    match projectee with | Q_Implicit  -> true | uu____150 -> false
  
let (uu___is_Q_Explicit : aqualv -> Prims.bool) =
  fun projectee  ->
    match projectee with | Q_Explicit  -> true | uu____154 -> false
  
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
  | Tv_Uvar of (FStar_BigInt.t,typ) FStar_Pervasives_Native.tuple2 
  | Tv_Let of
  (Prims.bool,FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple4 
  | Tv_Match of (FStar_Syntax_Syntax.term,branch Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Tv_Unknown [@@deriving show]
let (uu___is_Tv_Var : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Var _0 -> true | uu____241 -> false
  
let (__proj__Tv_Var__item___0 : term_view -> FStar_Syntax_Syntax.binder) =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0 
let (uu___is_Tv_FVar : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____253 -> false
  
let (__proj__Tv_FVar__item___0 : term_view -> FStar_Syntax_Syntax.fv) =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0 
let (uu___is_Tv_App : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_App _0 -> true | uu____269 -> false
  
let (__proj__Tv_App__item___0 :
  term_view -> (FStar_Syntax_Syntax.term,argv) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tv_App _0 -> _0 
let (uu___is_Tv_Abs : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Abs _0 -> true | uu____297 -> false
  
let (__proj__Tv_Abs__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tv_Abs _0 -> _0 
let (uu___is_Tv_Arrow : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Arrow _0 -> true | uu____325 -> false
  
let (__proj__Tv_Arrow__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tv_Arrow _0 -> _0 
let (uu___is_Tv_Type : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____349 -> false
  
let (__proj__Tv_Type__item___0 : term_view -> Prims.unit) =
  fun projectee  -> () 
let (uu___is_Tv_Refine : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Refine _0 -> true | uu____365 -> false
  
let (__proj__Tv_Refine__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tv_Refine _0 -> _0 
let (uu___is_Tv_Const : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____389 -> false
  
let (__proj__Tv_Const__item___0 : term_view -> vconst) =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0 
let (uu___is_Tv_Uvar : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Uvar _0 -> true | uu____405 -> false
  
let (__proj__Tv_Uvar__item___0 :
  term_view -> (FStar_BigInt.t,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Tv_Uvar _0 -> _0 
let (uu___is_Tv_Let : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Let _0 -> true | uu____437 -> false
  
let (__proj__Tv_Let__item___0 :
  term_view ->
    (Prims.bool,FStar_Syntax_Syntax.binder,FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Tv_Let _0 -> _0 
let (uu___is_Tv_Match : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Match _0 -> true | uu____479 -> false
  
let (__proj__Tv_Match__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.term,branch Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tv_Match _0 -> _0 
let (uu___is_Tv_Unknown : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Unknown  -> true | uu____508 -> false
  
type comp_view =
  | C_Total of typ 
  | C_Lemma of (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple2 
  | C_Unknown [@@deriving show]
let (uu___is_C_Total : comp_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Total _0 -> true | uu____525 -> false
  
let (__proj__C_Total__item___0 : comp_view -> typ) =
  fun projectee  -> match projectee with | C_Total _0 -> _0 
let (uu___is_C_Lemma : comp_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Lemma _0 -> true | uu____541 -> false
  
let (__proj__C_Lemma__item___0 :
  comp_view ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | C_Lemma _0 -> _0 
let (uu___is_C_Unknown : comp_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Unknown  -> true | uu____564 -> false
  
type sigelt_view =
  | Sg_Let of (FStar_Syntax_Syntax.fv,typ,FStar_Syntax_Syntax.term)
  FStar_Pervasives_Native.tuple3 
  | Sg_Inductive of
  (name,FStar_Syntax_Syntax.binder Prims.list,typ,name Prims.list)
  FStar_Pervasives_Native.tuple4 
  | Sg_Constructor of (name,typ) FStar_Pervasives_Native.tuple2 
  | Unk [@@deriving show]
let (uu___is_Sg_Let : sigelt_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sg_Let _0 -> true | uu____609 -> false
  
let (__proj__Sg_Let__item___0 :
  sigelt_view ->
    (FStar_Syntax_Syntax.fv,typ,FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Sg_Let _0 -> _0 
let (uu___is_Sg_Inductive : sigelt_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sg_Inductive _0 -> true | uu____651 -> false
  
let (__proj__Sg_Inductive__item___0 :
  sigelt_view ->
    (name,FStar_Syntax_Syntax.binder Prims.list,typ,name Prims.list)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Sg_Inductive _0 -> _0 
let (uu___is_Sg_Constructor : sigelt_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sg_Constructor _0 -> true | uu____703 -> false
  
let (__proj__Sg_Constructor__item___0 :
  sigelt_view -> (name,typ) FStar_Pervasives_Native.tuple2) =
  fun projectee  -> match projectee with | Sg_Constructor _0 -> _0 
let (uu___is_Unk : sigelt_view -> Prims.bool) =
  fun projectee  -> match projectee with | Unk  -> true | uu____726 -> false 
type refl_constant = {
  lid: FStar_Ident.lid ;
  t: FStar_Syntax_Syntax.term }[@@deriving show]
let (__proj__Mkrefl_constant__item__lid : refl_constant -> FStar_Ident.lid) =
  fun projectee  ->
    match projectee with
    | { lid = __fname__lid; t = __fname__t;_} -> __fname__lid
  
let (__proj__Mkrefl_constant__item__t :
  refl_constant -> FStar_Syntax_Syntax.term) =
  fun projectee  ->
    match projectee with
    | { lid = __fname__lid; t = __fname__t;_} -> __fname__t
  
let (fstar_refl_lid : Prims.string Prims.list -> FStar_Ident.lident) =
  fun s  ->
    FStar_Ident.lid_of_path (FStar_List.append ["FStar"; "Reflection"] s)
      FStar_Range.dummyRange
  
let (fstar_refl_basic_lid : Prims.string -> FStar_Ident.lident) =
  fun s  -> fstar_refl_lid ["Basic"; s] 
let (fstar_refl_syntax_lid : Prims.string -> FStar_Ident.lident) =
  fun s  -> fstar_refl_lid ["Syntax"; s] 
let (fstar_refl_types_lid : Prims.string -> FStar_Ident.lident) =
  fun s  -> fstar_refl_lid ["Types"; s] 
let (fstar_refl_data_lid : Prims.string -> FStar_Ident.lident) =
  fun s  -> fstar_refl_lid ["Data"; s] 
let (fstar_refl_data_const : Prims.string -> refl_constant) =
  fun s  ->
    let lid = fstar_refl_data_lid s  in
    let uu____768 = FStar_Syntax_Syntax.tdataconstr lid  in
    { lid; t = uu____768 }
  
let (mk_refl_types_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____772 = fstar_refl_types_lid s  in
    FStar_Syntax_Syntax.tconst uu____772
  
let (mk_refl_syntax_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____776 = fstar_refl_syntax_lid s  in
    FStar_Syntax_Syntax.tconst uu____776
  
let (mk_refl_data_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____780 = fstar_refl_data_lid s  in
    FStar_Syntax_Syntax.tconst uu____780
  
let (fstar_refl_inspect_lid : FStar_Ident.lident) =
  fstar_refl_basic_lid "inspect" 
let (fstar_refl_inspect : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar fstar_refl_inspect_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (fstar_refl_pack_lid : FStar_Ident.lident) = fstar_refl_basic_lid "pack" 
let (fstar_refl_pack : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar fstar_refl_pack_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (fstar_refl_pack_fv_lid : FStar_Ident.lident) =
  fstar_refl_basic_lid "pack_fv" 
let (fstar_refl_pack_fv : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.fvar fstar_refl_pack_fv_lid
    (FStar_Syntax_Syntax.Delta_defined_at_level (Prims.parse_int "1"))
    FStar_Pervasives_Native.None
  
let (fstar_refl_env : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "env" 
let (fstar_refl_fv : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "fv" 
let (fstar_refl_comp : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "comp" 
let (fstar_refl_binder : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "binder" 
let (fstar_refl_sigelt : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "sigelt" 
let (fstar_refl_aqualv : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "aqualv" 
let (fstar_refl_comp_view : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "comp_view" 
let (fstar_refl_term_view : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "term_view" 
let (fstar_refl_pattern : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "pattern" 
let (fstar_refl_branch : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "branch" 
let (ref_Q_Explicit : refl_constant) = fstar_refl_data_const "Q_Explicit" 
let (ref_Q_Implicit : refl_constant) = fstar_refl_data_const "Q_Implicit" 
let (ref_C_Unit : refl_constant) = fstar_refl_data_const "C_Unit" 
let (ref_C_True : refl_constant) = fstar_refl_data_const "C_True" 
let (ref_C_False : refl_constant) = fstar_refl_data_const "C_False" 
let (ref_C_Int : refl_constant) = fstar_refl_data_const "C_Int" 
let (ref_C_String : refl_constant) = fstar_refl_data_const "C_String" 
let (ref_Pat_Constant : refl_constant) = fstar_refl_data_const "Pat_Constant" 
let (ref_Pat_Cons : refl_constant) = fstar_refl_data_const "Pat_Cons" 
let (ref_Pat_Var : refl_constant) = fstar_refl_data_const "Pat_Var" 
let (ref_Pat_Wild : refl_constant) = fstar_refl_data_const "Pat_Wild" 
let (ref_Tv_Var : refl_constant) = fstar_refl_data_const "Tv_Var" 
let (ref_Tv_FVar : refl_constant) = fstar_refl_data_const "Tv_FVar" 
let (ref_Tv_App : refl_constant) = fstar_refl_data_const "Tv_App" 
let (ref_Tv_Abs : refl_constant) = fstar_refl_data_const "Tv_Abs" 
let (ref_Tv_Arrow : refl_constant) = fstar_refl_data_const "Tv_Arrow" 
let (ref_Tv_Type : refl_constant) = fstar_refl_data_const "Tv_Type" 
let (ref_Tv_Refine : refl_constant) = fstar_refl_data_const "Tv_Refine" 
let (ref_Tv_Const : refl_constant) = fstar_refl_data_const "Tv_Const" 
let (ref_Tv_Uvar : refl_constant) = fstar_refl_data_const "Tv_Uvar" 
let (ref_Tv_Let : refl_constant) = fstar_refl_data_const "Tv_Let" 
let (ref_Tv_Match : refl_constant) = fstar_refl_data_const "Tv_Match" 
let (ref_Tv_Unknown : refl_constant) = fstar_refl_data_const "Tv_Unknown" 
let (ref_C_Total : refl_constant) = fstar_refl_data_const "C_Total" 
let (ref_C_Lemma : refl_constant) = fstar_refl_data_const "C_Lemma" 
let (ref_C_Unknown : refl_constant) = fstar_refl_data_const "C_Unknown" 
let (ref_Sg_Let : refl_constant) = fstar_refl_data_const "Sg_Let" 
let (ref_Sg_Inductive : refl_constant) = fstar_refl_data_const "Sg_Inductive" 
let (ref_Sg_Constructor : refl_constant) =
  fstar_refl_data_const "Sg_Constructor" 
let (ref_Unk : refl_constant) = fstar_refl_data_const "Unk" 
let (ord_Lt_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Lt"] FStar_Range.dummyRange 
let (ord_Eq_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Eq"] FStar_Range.dummyRange 
let (ord_Gt_lid : FStar_Ident.lident) =
  FStar_Ident.lid_of_path ["FStar"; "Order"; "Gt"] FStar_Range.dummyRange 
let (ord_Lt : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr ord_Lt_lid 
let (ord_Eq : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr ord_Eq_lid 
let (ord_Gt : FStar_Syntax_Syntax.term) =
  FStar_Syntax_Syntax.tdataconstr ord_Gt_lid 