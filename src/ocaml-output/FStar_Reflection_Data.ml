open Prims
type name = Prims.string Prims.list
type typ = FStar_Syntax_Syntax.term
type binders = FStar_Syntax_Syntax.binder Prims.list
type vconst =
  | C_Unit 
  | C_Int of FStar_BigInt.t 
  | C_True 
  | C_False 
  | C_String of Prims.string 
  | C_Range of FStar_Range.range 
  | C_Reify 
  | C_Reflect of name 
let (uu___is_C_Unit : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Unit  -> true | uu____37573 -> false
  
let (uu___is_C_Int : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Int _0 -> true | uu____37585 -> false
  
let (__proj__C_Int__item___0 : vconst -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | C_Int _0 -> _0 
let (uu___is_C_True : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_True  -> true | uu____37603 -> false
  
let (uu___is_C_False : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_False  -> true | uu____37614 -> false
  
let (uu___is_C_String : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_String _0 -> true | uu____37627 -> false
  
let (__proj__C_String__item___0 : vconst -> Prims.string) =
  fun projectee  -> match projectee with | C_String _0 -> _0 
let (uu___is_C_Range : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Range _0 -> true | uu____37649 -> false
  
let (__proj__C_Range__item___0 : vconst -> FStar_Range.range) =
  fun projectee  -> match projectee with | C_Range _0 -> _0 
let (uu___is_C_Reify : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Reify  -> true | uu____37667 -> false
  
let (uu___is_C_Reflect : vconst -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Reflect _0 -> true | uu____37679 -> false
  
let (__proj__C_Reflect__item___0 : vconst -> name) =
  fun projectee  -> match projectee with | C_Reflect _0 -> _0 
type pattern =
  | Pat_Constant of vconst 
  | Pat_Cons of (FStar_Syntax_Syntax.fv * pattern Prims.list) 
  | Pat_Var of FStar_Syntax_Syntax.bv 
  | Pat_Wild of FStar_Syntax_Syntax.bv 
  | Pat_Dot_Term of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) 
let (uu___is_Pat_Constant : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_Constant _0 -> true | uu____37733 -> false
  
let (__proj__Pat_Constant__item___0 : pattern -> vconst) =
  fun projectee  -> match projectee with | Pat_Constant _0 -> _0 
let (uu___is_Pat_Cons : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_Cons _0 -> true | uu____37758 -> false
  
let (__proj__Pat_Cons__item___0 :
  pattern -> (FStar_Syntax_Syntax.fv * pattern Prims.list)) =
  fun projectee  -> match projectee with | Pat_Cons _0 -> _0 
let (uu___is_Pat_Var : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_Var _0 -> true | uu____37795 -> false
  
let (__proj__Pat_Var__item___0 : pattern -> FStar_Syntax_Syntax.bv) =
  fun projectee  -> match projectee with | Pat_Var _0 -> _0 
let (uu___is_Pat_Wild : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_Wild _0 -> true | uu____37814 -> false
  
let (__proj__Pat_Wild__item___0 : pattern -> FStar_Syntax_Syntax.bv) =
  fun projectee  -> match projectee with | Pat_Wild _0 -> _0 
let (uu___is_Pat_Dot_Term : pattern -> Prims.bool) =
  fun projectee  ->
    match projectee with | Pat_Dot_Term _0 -> true | uu____37837 -> false
  
let (__proj__Pat_Dot_Term__item___0 :
  pattern -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | Pat_Dot_Term _0 -> _0 
type branch = (pattern * FStar_Syntax_Syntax.term)
type aqualv =
  | Q_Implicit 
  | Q_Explicit 
  | Q_Meta of FStar_Syntax_Syntax.term 
let (uu___is_Q_Implicit : aqualv -> Prims.bool) =
  fun projectee  ->
    match projectee with | Q_Implicit  -> true | uu____37876 -> false
  
let (uu___is_Q_Explicit : aqualv -> Prims.bool) =
  fun projectee  ->
    match projectee with | Q_Explicit  -> true | uu____37887 -> false
  
let (uu___is_Q_Meta : aqualv -> Prims.bool) =
  fun projectee  ->
    match projectee with | Q_Meta _0 -> true | uu____37899 -> false
  
let (__proj__Q_Meta__item___0 : aqualv -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | Q_Meta _0 -> _0 
type argv = (FStar_Syntax_Syntax.term * aqualv)
type term_view =
  | Tv_Var of FStar_Syntax_Syntax.bv 
  | Tv_BVar of FStar_Syntax_Syntax.bv 
  | Tv_FVar of FStar_Syntax_Syntax.fv 
  | Tv_App of (FStar_Syntax_Syntax.term * argv) 
  | Tv_Abs of (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term) 
  | Tv_Arrow of (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) 
  | Tv_Type of unit 
  | Tv_Refine of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) 
  | Tv_Const of vconst 
  | Tv_Uvar of (FStar_BigInt.t * FStar_Syntax_Syntax.ctx_uvar_and_subst) 
  | Tv_Let of (Prims.bool * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term
  * FStar_Syntax_Syntax.term) 
  | Tv_Match of (FStar_Syntax_Syntax.term * branch Prims.list) 
  | Tv_AscribedT of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) 
  | Tv_AscribedC of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) 
  | Tv_Unknown 
let (uu___is_Tv_Var : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Var _0 -> true | uu____38043 -> false
  
let (__proj__Tv_Var__item___0 : term_view -> FStar_Syntax_Syntax.bv) =
  fun projectee  -> match projectee with | Tv_Var _0 -> _0 
let (uu___is_Tv_BVar : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_BVar _0 -> true | uu____38062 -> false
  
let (__proj__Tv_BVar__item___0 : term_view -> FStar_Syntax_Syntax.bv) =
  fun projectee  -> match projectee with | Tv_BVar _0 -> _0 
let (uu___is_Tv_FVar : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_FVar _0 -> true | uu____38081 -> false
  
let (__proj__Tv_FVar__item___0 : term_view -> FStar_Syntax_Syntax.fv) =
  fun projectee  -> match projectee with | Tv_FVar _0 -> _0 
let (uu___is_Tv_App : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_App _0 -> true | uu____38104 -> false
  
let (__proj__Tv_App__item___0 :
  term_view -> (FStar_Syntax_Syntax.term * argv)) =
  fun projectee  -> match projectee with | Tv_App _0 -> _0 
let (uu___is_Tv_Abs : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Abs _0 -> true | uu____38139 -> false
  
let (__proj__Tv_Abs__item___0 :
  term_view -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | Tv_Abs _0 -> _0 
let (uu___is_Tv_Arrow : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Arrow _0 -> true | uu____38174 -> false
  
let (__proj__Tv_Arrow__item___0 :
  term_view -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)) =
  fun projectee  -> match projectee with | Tv_Arrow _0 -> _0 
let (uu___is_Tv_Type : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Type _0 -> true | uu____38205 -> false
  

let (uu___is_Tv_Refine : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Refine _0 -> true | uu____38223 -> false
  
let (__proj__Tv_Refine__item___0 :
  term_view -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | Tv_Refine _0 -> _0 
let (uu___is_Tv_Const : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Const _0 -> true | uu____38254 -> false
  
let (__proj__Tv_Const__item___0 : term_view -> vconst) =
  fun projectee  -> match projectee with | Tv_Const _0 -> _0 
let (uu___is_Tv_Uvar : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Uvar _0 -> true | uu____38277 -> false
  
let (__proj__Tv_Uvar__item___0 :
  term_view -> (FStar_BigInt.t * FStar_Syntax_Syntax.ctx_uvar_and_subst)) =
  fun projectee  -> match projectee with | Tv_Uvar _0 -> _0 
let (uu___is_Tv_Let : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Let _0 -> true | uu____38317 -> false
  
let (__proj__Tv_Let__item___0 :
  term_view ->
    (Prims.bool * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | Tv_Let _0 -> _0 
let (uu___is_Tv_Match : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Match _0 -> true | uu____38369 -> false
  
let (__proj__Tv_Match__item___0 :
  term_view -> (FStar_Syntax_Syntax.term * branch Prims.list)) =
  fun projectee  -> match projectee with | Tv_Match _0 -> _0 
let (uu___is_Tv_AscribedT : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_AscribedT _0 -> true | uu____38414 -> false
  
let (__proj__Tv_AscribedT__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tv_AscribedT _0 -> _0 
let (uu___is_Tv_AscribedC : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_AscribedC _0 -> true | uu____38465 -> false
  
let (__proj__Tv_AscribedC__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tv_AscribedC _0 -> _0 
let (uu___is_Tv_Unknown : term_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tv_Unknown  -> true | uu____38507 -> false
  
type bv_view =
  {
  bv_ppname: Prims.string ;
  bv_index: FStar_BigInt.t ;
  bv_sort: typ }
let (__proj__Mkbv_view__item__bv_ppname : bv_view -> Prims.string) =
  fun projectee  ->
    match projectee with | { bv_ppname; bv_index; bv_sort;_} -> bv_ppname
  
let (__proj__Mkbv_view__item__bv_index : bv_view -> FStar_BigInt.t) =
  fun projectee  ->
    match projectee with | { bv_ppname; bv_index; bv_sort;_} -> bv_index
  
let (__proj__Mkbv_view__item__bv_sort : bv_view -> typ) =
  fun projectee  ->
    match projectee with | { bv_ppname; bv_index; bv_sort;_} -> bv_sort
  
type binder_view = (FStar_Syntax_Syntax.bv * aqualv)
type comp_view =
  | C_Total of (typ * FStar_Syntax_Syntax.term
  FStar_Pervasives_Native.option) 
  | C_Lemma of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) 
  | C_Unknown 
let (uu___is_C_Total : comp_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Total _0 -> true | uu____38597 -> false
  
let (__proj__C_Total__item___0 :
  comp_view ->
    (typ * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | C_Total _0 -> _0 
let (uu___is_C_Lemma : comp_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Lemma _0 -> true | uu____38638 -> false
  
let (__proj__C_Lemma__item___0 :
  comp_view -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)) =
  fun projectee  -> match projectee with | C_Lemma _0 -> _0 
let (uu___is_C_Unknown : comp_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | C_Unknown  -> true | uu____38668 -> false
  
type sigelt_view =
  | Sg_Let of (Prims.bool * FStar_Syntax_Syntax.fv *
  FStar_Syntax_Syntax.univ_name Prims.list * typ * FStar_Syntax_Syntax.term)
  
  | Sg_Inductive of (name * FStar_Syntax_Syntax.univ_name Prims.list *
  FStar_Syntax_Syntax.binder Prims.list * typ * name Prims.list) 
  | Sg_Constructor of (name * typ) 
  | Unk 
let (uu___is_Sg_Let : sigelt_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sg_Let _0 -> true | uu____38741 -> false
  
let (__proj__Sg_Let__item___0 :
  sigelt_view ->
    (Prims.bool * FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.univ_name
      Prims.list * typ * FStar_Syntax_Syntax.term))
  = fun projectee  -> match projectee with | Sg_Let _0 -> _0 
let (uu___is_Sg_Inductive : sigelt_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sg_Inductive _0 -> true | uu____38815 -> false
  
let (__proj__Sg_Inductive__item___0 :
  sigelt_view ->
    (name * FStar_Syntax_Syntax.univ_name Prims.list *
      FStar_Syntax_Syntax.binder Prims.list * typ * name Prims.list))
  = fun projectee  -> match projectee with | Sg_Inductive _0 -> _0 
let (uu___is_Sg_Constructor : sigelt_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Sg_Constructor _0 -> true | uu____38886 -> false
  
let (__proj__Sg_Constructor__item___0 : sigelt_view -> (name * typ)) =
  fun projectee  -> match projectee with | Sg_Constructor _0 -> _0 
let (uu___is_Unk : sigelt_view -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unk  -> true | uu____38916 -> false
  
type var = FStar_BigInt.t
type exp =
  | Unit 
  | Var of var 
  | Mult of (exp * exp) 
let (uu___is_Unit : exp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unit  -> true | uu____38941 -> false
  
let (uu___is_Var : exp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____38953 -> false
  
let (__proj__Var__item___0 : exp -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Mult : exp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Mult _0 -> true | uu____38976 -> false
  
let (__proj__Mult__item___0 : exp -> (exp * exp)) =
  fun projectee  -> match projectee with | Mult _0 -> _0 
type refl_constant =
  {
  lid: FStar_Ident.lid ;
  fv: FStar_Syntax_Syntax.fv ;
  t: FStar_Syntax_Syntax.term }
let (__proj__Mkrefl_constant__item__lid : refl_constant -> FStar_Ident.lid) =
  fun projectee  -> match projectee with | { lid; fv; t;_} -> lid 
let (__proj__Mkrefl_constant__item__fv :
  refl_constant -> FStar_Syntax_Syntax.fv) =
  fun projectee  -> match projectee with | { lid; fv; t;_} -> fv 
let (__proj__Mkrefl_constant__item__t :
  refl_constant -> FStar_Syntax_Syntax.term) =
  fun projectee  -> match projectee with | { lid; fv; t;_} -> t 
let (refl_constant_lid : refl_constant -> FStar_Ident.lid) =
  fun rc  -> rc.lid 
let (refl_constant_term : refl_constant -> FStar_Syntax_Syntax.term) =
  fun rc  -> rc.t 
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
    let uu____39126 =
      FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant
        (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
       in
    let uu____39127 = FStar_Syntax_Syntax.tdataconstr lid  in
    { lid; fv = uu____39126; t = uu____39127 }
  
let (mk_refl_types_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____39136 = fstar_refl_types_lid s  in
    FStar_Syntax_Syntax.tconst uu____39136
  
let (mk_refl_types_lid_as_fv : Prims.string -> FStar_Syntax_Syntax.fv) =
  fun s  ->
    let uu____39145 = fstar_refl_types_lid s  in
    FStar_Syntax_Syntax.fvconst uu____39145
  
let (mk_refl_syntax_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____39154 = fstar_refl_syntax_lid s  in
    FStar_Syntax_Syntax.tconst uu____39154
  
let (mk_refl_syntax_lid_as_fv : Prims.string -> FStar_Syntax_Syntax.fv) =
  fun s  ->
    let uu____39163 = fstar_refl_syntax_lid s  in
    FStar_Syntax_Syntax.fvconst uu____39163
  
let (mk_refl_data_lid_as_term : Prims.string -> FStar_Syntax_Syntax.term) =
  fun s  ->
    let uu____39172 = fstar_refl_data_lid s  in
    FStar_Syntax_Syntax.tconst uu____39172
  
let (mk_refl_data_lid_as_fv : Prims.string -> FStar_Syntax_Syntax.fv) =
  fun s  ->
    let uu____39181 = fstar_refl_data_lid s  in
    FStar_Syntax_Syntax.fvconst uu____39181
  
let (mk_inspect_pack_pair : Prims.string -> (refl_constant * refl_constant))
  =
  fun s  ->
    let inspect_lid = fstar_refl_basic_lid (Prims.op_Hat "inspect" s)  in
    let pack_lid = fstar_refl_basic_lid (Prims.op_Hat "pack" s)  in
    let inspect_fv =
      FStar_Syntax_Syntax.lid_as_fv inspect_lid
        (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "1"))
        FStar_Pervasives_Native.None
       in
    let pack_fv =
      FStar_Syntax_Syntax.lid_as_fv pack_lid
        (FStar_Syntax_Syntax.Delta_constant_at_level (Prims.parse_int "1"))
        FStar_Pervasives_Native.None
       in
    let inspect =
      let uu____39203 = FStar_Syntax_Syntax.fv_to_tm inspect_fv  in
      { lid = inspect_lid; fv = inspect_fv; t = uu____39203 }  in
    let pack =
      let uu____39205 = FStar_Syntax_Syntax.fv_to_tm pack_fv  in
      { lid = pack_lid; fv = pack_fv; t = uu____39205 }  in
    (inspect, pack)
  
let (uu___462 : (refl_constant * refl_constant)) = mk_inspect_pack_pair "_ln" 
let (fstar_refl_inspect_ln : refl_constant) =
  match uu___462 with
  | (fstar_refl_inspect_ln,fstar_refl_pack_ln) -> fstar_refl_inspect_ln 
let (fstar_refl_pack_ln : refl_constant) =
  match uu___462 with
  | (fstar_refl_inspect_ln1,fstar_refl_pack_ln) -> fstar_refl_pack_ln 
let (uu___469 : (refl_constant * refl_constant)) = mk_inspect_pack_pair "_fv" 
let (fstar_refl_inspect_fv : refl_constant) =
  match uu___469 with
  | (fstar_refl_inspect_fv,fstar_refl_pack_fv) -> fstar_refl_inspect_fv 
let (fstar_refl_pack_fv : refl_constant) =
  match uu___469 with
  | (fstar_refl_inspect_fv1,fstar_refl_pack_fv) -> fstar_refl_pack_fv 
let (uu___476 : (refl_constant * refl_constant)) = mk_inspect_pack_pair "_bv" 
let (fstar_refl_inspect_bv : refl_constant) =
  match uu___476 with
  | (fstar_refl_inspect_bv,fstar_refl_pack_bv) -> fstar_refl_inspect_bv 
let (fstar_refl_pack_bv : refl_constant) =
  match uu___476 with
  | (fstar_refl_inspect_bv1,fstar_refl_pack_bv) -> fstar_refl_pack_bv 
let (uu___483 : (refl_constant * refl_constant)) =
  mk_inspect_pack_pair "_binder" 
let (fstar_refl_inspect_binder : refl_constant) =
  match uu___483 with
  | (fstar_refl_inspect_binder,fstar_refl_pack_binder) ->
      fstar_refl_inspect_binder
  
let (fstar_refl_pack_binder : refl_constant) =
  match uu___483 with
  | (fstar_refl_inspect_binder1,fstar_refl_pack_binder) ->
      fstar_refl_pack_binder
  
let (uu___490 : (refl_constant * refl_constant)) =
  mk_inspect_pack_pair "_comp" 
let (fstar_refl_inspect_comp : refl_constant) =
  match uu___490 with
  | (fstar_refl_inspect_comp,fstar_refl_pack_comp) -> fstar_refl_inspect_comp 
let (fstar_refl_pack_comp : refl_constant) =
  match uu___490 with
  | (fstar_refl_inspect_comp1,fstar_refl_pack_comp) -> fstar_refl_pack_comp 
let (uu___497 : (refl_constant * refl_constant)) =
  mk_inspect_pack_pair "_sigelt" 
let (fstar_refl_inspect_sigelt : refl_constant) =
  match uu___497 with
  | (fstar_refl_inspect_sigelt,fstar_refl_pack_sigelt) ->
      fstar_refl_inspect_sigelt
  
let (fstar_refl_pack_sigelt : refl_constant) =
  match uu___497 with
  | (fstar_refl_inspect_sigelt1,fstar_refl_pack_sigelt) ->
      fstar_refl_pack_sigelt
  
let (fstar_refl_env : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "env" 
let (fstar_refl_env_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "env" 
let (fstar_refl_bv : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "bv" 
let (fstar_refl_bv_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "bv" 
let (fstar_refl_fv : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "fv" 
let (fstar_refl_fv_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "fv" 
let (fstar_refl_comp : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "comp" 
let (fstar_refl_comp_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "comp" 
let (fstar_refl_binder : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "binder" 
let (fstar_refl_binder_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "binder" 
let (fstar_refl_sigelt : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "sigelt" 
let (fstar_refl_sigelt_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "sigelt" 
let (fstar_refl_term : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "term" 
let (fstar_refl_term_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "term" 
let (fstar_refl_ident : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "ident" 
let (fstar_refl_ident_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "ident" 
let (fstar_refl_univ_name : FStar_Syntax_Syntax.term) =
  mk_refl_types_lid_as_term "univ_name" 
let (fstar_refl_univ_name_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_types_lid_as_fv "univ_name" 
let (fstar_refl_aqualv : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "aqualv" 
let (fstar_refl_aqualv_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "aqualv" 
let (fstar_refl_comp_view : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "comp_view" 
let (fstar_refl_comp_view_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "comp_view" 
let (fstar_refl_term_view : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "term_view" 
let (fstar_refl_term_view_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "term_view" 
let (fstar_refl_pattern : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "pattern" 
let (fstar_refl_pattern_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "pattern" 
let (fstar_refl_branch : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "branch" 
let (fstar_refl_branch_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "branch" 
let (fstar_refl_bv_view : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "bv_view" 
let (fstar_refl_bv_view_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "bv_view" 
let (fstar_refl_vconst : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "vconst" 
let (fstar_refl_vconst_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "vconst" 
let (fstar_refl_sigelt_view : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "sigelt_view" 
let (fstar_refl_sigelt_view_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "sigelt_view" 
let (fstar_refl_exp : FStar_Syntax_Syntax.term) =
  mk_refl_data_lid_as_term "exp" 
let (fstar_refl_exp_fv : FStar_Syntax_Syntax.fv) =
  mk_refl_data_lid_as_fv "exp" 
let (ref_Mk_bv : refl_constant) =
  let lid = fstar_refl_data_lid "Mkbv_view"  in
  let attr =
    let uu____39354 =
      let uu____39361 = fstar_refl_data_lid "bv_view"  in
      let uu____39363 =
        let uu____39366 =
          FStar_Ident.mk_ident ("bv_ppname", FStar_Range.dummyRange)  in
        let uu____39369 =
          let uu____39372 =
            FStar_Ident.mk_ident ("bv_index", FStar_Range.dummyRange)  in
          let uu____39375 =
            let uu____39378 =
              FStar_Ident.mk_ident ("bv_sort", FStar_Range.dummyRange)  in
            [uu____39378]  in
          uu____39372 :: uu____39375  in
        uu____39366 :: uu____39369  in
      (uu____39361, uu____39363)  in
    FStar_Syntax_Syntax.Record_ctor uu____39354  in
  let fv =
    FStar_Syntax_Syntax.lid_as_fv lid FStar_Syntax_Syntax.delta_constant
      (FStar_Pervasives_Native.Some attr)
     in
  let uu____39384 = FStar_Syntax_Syntax.fv_to_tm fv  in
  { lid; fv; t = uu____39384 } 
let (ref_Q_Explicit : refl_constant) = fstar_refl_data_const "Q_Explicit" 
let (ref_Q_Implicit : refl_constant) = fstar_refl_data_const "Q_Implicit" 
let (ref_Q_Meta : refl_constant) = fstar_refl_data_const "Q_Meta" 
let (ref_C_Unit : refl_constant) = fstar_refl_data_const "C_Unit" 
let (ref_C_True : refl_constant) = fstar_refl_data_const "C_True" 
let (ref_C_False : refl_constant) = fstar_refl_data_const "C_False" 
let (ref_C_Int : refl_constant) = fstar_refl_data_const "C_Int" 
let (ref_C_String : refl_constant) = fstar_refl_data_const "C_String" 
let (ref_C_Range : refl_constant) = fstar_refl_data_const "C_Range" 
let (ref_C_Reify : refl_constant) = fstar_refl_data_const "C_Reify" 
let (ref_C_Reflect : refl_constant) = fstar_refl_data_const "C_Reflect" 
let (ref_Pat_Constant : refl_constant) = fstar_refl_data_const "Pat_Constant" 
let (ref_Pat_Cons : refl_constant) = fstar_refl_data_const "Pat_Cons" 
let (ref_Pat_Var : refl_constant) = fstar_refl_data_const "Pat_Var" 
let (ref_Pat_Wild : refl_constant) = fstar_refl_data_const "Pat_Wild" 
let (ref_Pat_Dot_Term : refl_constant) = fstar_refl_data_const "Pat_Dot_Term" 
let (ref_Tv_Var : refl_constant) = fstar_refl_data_const "Tv_Var" 
let (ref_Tv_BVar : refl_constant) = fstar_refl_data_const "Tv_BVar" 
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
let (ref_Tv_AscT : refl_constant) = fstar_refl_data_const "Tv_AscribedT" 
let (ref_Tv_AscC : refl_constant) = fstar_refl_data_const "Tv_AscribedC" 
let (ref_Tv_Unknown : refl_constant) = fstar_refl_data_const "Tv_Unknown" 
let (ref_C_Total : refl_constant) = fstar_refl_data_const "C_Total" 
let (ref_C_Lemma : refl_constant) = fstar_refl_data_const "C_Lemma" 
let (ref_C_Unknown : refl_constant) = fstar_refl_data_const "C_Unknown" 
let (ref_Sg_Let : refl_constant) = fstar_refl_data_const "Sg_Let" 
let (ref_Sg_Inductive : refl_constant) = fstar_refl_data_const "Sg_Inductive" 
let (ref_Sg_Constructor : refl_constant) =
  fstar_refl_data_const "Sg_Constructor" 
let (ref_Unk : refl_constant) = fstar_refl_data_const "Unk" 
let (ref_E_Unit : refl_constant) = fstar_refl_data_const "Unit" 
let (ref_E_Var : refl_constant) = fstar_refl_data_const "Var" 
let (ref_E_Mult : refl_constant) = fstar_refl_data_const "Mult" 
let (t_exp : FStar_Syntax_Syntax.term) =
  let uu____39468 =
    FStar_Ident.lid_of_path ["FStar"; "Reflection"; "Data"; "exp"]
      FStar_Range.dummyRange
     in
  FStar_Syntax_Syntax.tconst uu____39468 
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
let (ord_Lt_fv : FStar_Syntax_Syntax.fv) =
  FStar_Syntax_Syntax.lid_as_fv ord_Lt_lid FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (ord_Eq_fv : FStar_Syntax_Syntax.fv) =
  FStar_Syntax_Syntax.lid_as_fv ord_Eq_lid FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  
let (ord_Gt_fv : FStar_Syntax_Syntax.fv) =
  FStar_Syntax_Syntax.lid_as_fv ord_Gt_lid FStar_Syntax_Syntax.delta_constant
    (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
  