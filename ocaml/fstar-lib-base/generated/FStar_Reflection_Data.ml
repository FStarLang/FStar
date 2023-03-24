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
  | C_Range of FStar_Compiler_Range.range 
  | C_Reify 
  | C_Reflect of name 
let (uu___is_C_Unit : vconst -> Prims.bool) =
  fun projectee -> match projectee with | C_Unit -> true | uu___ -> false
let (uu___is_C_Int : vconst -> Prims.bool) =
  fun projectee -> match projectee with | C_Int _0 -> true | uu___ -> false
let (__proj__C_Int__item___0 : vconst -> FStar_BigInt.t) =
  fun projectee -> match projectee with | C_Int _0 -> _0
let (uu___is_C_True : vconst -> Prims.bool) =
  fun projectee -> match projectee with | C_True -> true | uu___ -> false
let (uu___is_C_False : vconst -> Prims.bool) =
  fun projectee -> match projectee with | C_False -> true | uu___ -> false
let (uu___is_C_String : vconst -> Prims.bool) =
  fun projectee ->
    match projectee with | C_String _0 -> true | uu___ -> false
let (__proj__C_String__item___0 : vconst -> Prims.string) =
  fun projectee -> match projectee with | C_String _0 -> _0
let (uu___is_C_Range : vconst -> Prims.bool) =
  fun projectee -> match projectee with | C_Range _0 -> true | uu___ -> false
let (__proj__C_Range__item___0 : vconst -> FStar_Compiler_Range.range) =
  fun projectee -> match projectee with | C_Range _0 -> _0
let (uu___is_C_Reify : vconst -> Prims.bool) =
  fun projectee -> match projectee with | C_Reify -> true | uu___ -> false
let (uu___is_C_Reflect : vconst -> Prims.bool) =
  fun projectee ->
    match projectee with | C_Reflect _0 -> true | uu___ -> false
let (__proj__C_Reflect__item___0 : vconst -> name) =
  fun projectee -> match projectee with | C_Reflect _0 -> _0
type universes = FStar_Syntax_Syntax.universe Prims.list
type pattern =
  | Pat_Constant of vconst 
  | Pat_Cons of (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe
  Prims.list FStar_Pervasives_Native.option * (pattern * Prims.bool)
  Prims.list) 
  | Pat_Var of FStar_Syntax_Syntax.bv 
  | Pat_Wild of FStar_Syntax_Syntax.bv 
  | Pat_Dot_Term of FStar_Syntax_Syntax.term FStar_Pervasives_Native.option 
let (uu___is_Pat_Constant : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_Constant _0 -> true | uu___ -> false
let (__proj__Pat_Constant__item___0 : pattern -> vconst) =
  fun projectee -> match projectee with | Pat_Constant _0 -> _0
let (uu___is_Pat_Cons : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_Cons _0 -> true | uu___ -> false
let (__proj__Pat_Cons__item___0 :
  pattern ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list
      FStar_Pervasives_Native.option * (pattern * Prims.bool) Prims.list))
  = fun projectee -> match projectee with | Pat_Cons _0 -> _0
let (uu___is_Pat_Var : pattern -> Prims.bool) =
  fun projectee -> match projectee with | Pat_Var _0 -> true | uu___ -> false
let (__proj__Pat_Var__item___0 : pattern -> FStar_Syntax_Syntax.bv) =
  fun projectee -> match projectee with | Pat_Var _0 -> _0
let (uu___is_Pat_Wild : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_Wild _0 -> true | uu___ -> false
let (__proj__Pat_Wild__item___0 : pattern -> FStar_Syntax_Syntax.bv) =
  fun projectee -> match projectee with | Pat_Wild _0 -> _0
let (uu___is_Pat_Dot_Term : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_Dot_Term _0 -> true | uu___ -> false
let (__proj__Pat_Dot_Term__item___0 :
  pattern -> FStar_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | Pat_Dot_Term _0 -> _0
type branch = (pattern * FStar_Syntax_Syntax.term)
type aqualv =
  | Q_Implicit 
  | Q_Explicit 
  | Q_Meta of FStar_Syntax_Syntax.term 
let (uu___is_Q_Implicit : aqualv -> Prims.bool) =
  fun projectee -> match projectee with | Q_Implicit -> true | uu___ -> false
let (uu___is_Q_Explicit : aqualv -> Prims.bool) =
  fun projectee -> match projectee with | Q_Explicit -> true | uu___ -> false
let (uu___is_Q_Meta : aqualv -> Prims.bool) =
  fun projectee -> match projectee with | Q_Meta _0 -> true | uu___ -> false
let (__proj__Q_Meta__item___0 : aqualv -> FStar_Syntax_Syntax.term) =
  fun projectee -> match projectee with | Q_Meta _0 -> _0
type argv = (FStar_Syntax_Syntax.term * aqualv)
type universe_view =
  | Uv_Zero 
  | Uv_Succ of FStar_Syntax_Syntax.universe 
  | Uv_Max of universes 
  | Uv_BVar of FStar_BigInt.t 
  | Uv_Name of (Prims.string * FStar_Compiler_Range.range) 
  | Uv_Unif of FStar_Syntax_Syntax.universe_uvar 
  | Uv_Unk 
let (uu___is_Uv_Zero : universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Zero -> true | uu___ -> false
let (uu___is_Uv_Succ : universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Succ _0 -> true | uu___ -> false
let (__proj__Uv_Succ__item___0 :
  universe_view -> FStar_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Uv_Succ _0 -> _0
let (uu___is_Uv_Max : universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Max _0 -> true | uu___ -> false
let (__proj__Uv_Max__item___0 : universe_view -> universes) =
  fun projectee -> match projectee with | Uv_Max _0 -> _0
let (uu___is_Uv_BVar : universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_BVar _0 -> true | uu___ -> false
let (__proj__Uv_BVar__item___0 : universe_view -> FStar_BigInt.t) =
  fun projectee -> match projectee with | Uv_BVar _0 -> _0
let (uu___is_Uv_Name : universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Name _0 -> true | uu___ -> false
let (__proj__Uv_Name__item___0 :
  universe_view -> (Prims.string * FStar_Compiler_Range.range)) =
  fun projectee -> match projectee with | Uv_Name _0 -> _0
let (uu___is_Uv_Unif : universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Unif _0 -> true | uu___ -> false
let (__proj__Uv_Unif__item___0 :
  universe_view -> FStar_Syntax_Syntax.universe_uvar) =
  fun projectee -> match projectee with | Uv_Unif _0 -> _0
let (uu___is_Uv_Unk : universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Unk -> true | uu___ -> false
type term_view =
  | Tv_Var of FStar_Syntax_Syntax.bv 
  | Tv_BVar of FStar_Syntax_Syntax.bv 
  | Tv_FVar of FStar_Syntax_Syntax.fv 
  | Tv_UInst of (FStar_Syntax_Syntax.fv * universes) 
  | Tv_App of (FStar_Syntax_Syntax.term * argv) 
  | Tv_Abs of (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term) 
  | Tv_Arrow of (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp) 
  | Tv_Type of FStar_Syntax_Syntax.universe 
  | Tv_Refine of (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) 
  | Tv_Const of vconst 
  | Tv_Uvar of (FStar_BigInt.t * FStar_Syntax_Syntax.ctx_uvar_and_subst) 
  | Tv_Let of (Prims.bool * FStar_Syntax_Syntax.term Prims.list *
  FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term) 
  | Tv_Match of (FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.match_returns_ascription FStar_Pervasives_Native.option
  * branch Prims.list) 
  | Tv_AscribedT of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * Prims.bool) 
  | Tv_AscribedC of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * Prims.bool) 
  | Tv_Unknown 
let (uu___is_Tv_Var : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Var _0 -> true | uu___ -> false
let (__proj__Tv_Var__item___0 : term_view -> FStar_Syntax_Syntax.bv) =
  fun projectee -> match projectee with | Tv_Var _0 -> _0
let (uu___is_Tv_BVar : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_BVar _0 -> true | uu___ -> false
let (__proj__Tv_BVar__item___0 : term_view -> FStar_Syntax_Syntax.bv) =
  fun projectee -> match projectee with | Tv_BVar _0 -> _0
let (uu___is_Tv_FVar : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_FVar _0 -> true | uu___ -> false
let (__proj__Tv_FVar__item___0 : term_view -> FStar_Syntax_Syntax.fv) =
  fun projectee -> match projectee with | Tv_FVar _0 -> _0
let (uu___is_Tv_UInst : term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_UInst _0 -> true | uu___ -> false
let (__proj__Tv_UInst__item___0 :
  term_view -> (FStar_Syntax_Syntax.fv * universes)) =
  fun projectee -> match projectee with | Tv_UInst _0 -> _0
let (uu___is_Tv_App : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_App _0 -> true | uu___ -> false
let (__proj__Tv_App__item___0 :
  term_view -> (FStar_Syntax_Syntax.term * argv)) =
  fun projectee -> match projectee with | Tv_App _0 -> _0
let (uu___is_Tv_Abs : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Abs _0 -> true | uu___ -> false
let (__proj__Tv_Abs__item___0 :
  term_view -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.term)) =
  fun projectee -> match projectee with | Tv_Abs _0 -> _0
let (uu___is_Tv_Arrow : term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Arrow _0 -> true | uu___ -> false
let (__proj__Tv_Arrow__item___0 :
  term_view -> (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.comp)) =
  fun projectee -> match projectee with | Tv_Arrow _0 -> _0
let (uu___is_Tv_Type : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Type _0 -> true | uu___ -> false
let (__proj__Tv_Type__item___0 : term_view -> FStar_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Tv_Type _0 -> _0
let (uu___is_Tv_Refine : term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Refine _0 -> true | uu___ -> false
let (__proj__Tv_Refine__item___0 :
  term_view -> (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term)) =
  fun projectee -> match projectee with | Tv_Refine _0 -> _0
let (uu___is_Tv_Const : term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Const _0 -> true | uu___ -> false
let (__proj__Tv_Const__item___0 : term_view -> vconst) =
  fun projectee -> match projectee with | Tv_Const _0 -> _0
let (uu___is_Tv_Uvar : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Uvar _0 -> true | uu___ -> false
let (__proj__Tv_Uvar__item___0 :
  term_view -> (FStar_BigInt.t * FStar_Syntax_Syntax.ctx_uvar_and_subst)) =
  fun projectee -> match projectee with | Tv_Uvar _0 -> _0
let (uu___is_Tv_Let : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Let _0 -> true | uu___ -> false
let (__proj__Tv_Let__item___0 :
  term_view ->
    (Prims.bool * FStar_Syntax_Syntax.term Prims.list *
      FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term))
  = fun projectee -> match projectee with | Tv_Let _0 -> _0
let (uu___is_Tv_Match : term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Match _0 -> true | uu___ -> false
let (__proj__Tv_Match__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.match_returns_ascription
      FStar_Pervasives_Native.option * branch Prims.list))
  = fun projectee -> match projectee with | Tv_Match _0 -> _0
let (uu___is_Tv_AscribedT : term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_AscribedT _0 -> true | uu___ -> false
let (__proj__Tv_AscribedT__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * Prims.bool))
  = fun projectee -> match projectee with | Tv_AscribedT _0 -> _0
let (uu___is_Tv_AscribedC : term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_AscribedC _0 -> true | uu___ -> false
let (__proj__Tv_AscribedC__item___0 :
  term_view ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.comp *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option * Prims.bool))
  = fun projectee -> match projectee with | Tv_AscribedC _0 -> _0
let (uu___is_Tv_Unknown : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Unknown -> true | uu___ -> false
type qualifier =
  | Assumption 
  | InternalAssumption 
  | New 
  | Private 
  | Unfold_for_unification_and_vcgen 
  | Visible_default 
  | Irreducible 
  | Inline_for_extraction 
  | NoExtract 
  | Noeq 
  | Unopteq 
  | TotalEffect 
  | Logic 
  | Reifiable 
  | Reflectable of FStar_Ident.lid 
  | Discriminator of FStar_Ident.lid 
  | Projector of (FStar_Ident.lid * FStar_Ident.ident) 
  | RecordType of (FStar_Ident.ident Prims.list * FStar_Ident.ident
  Prims.list) 
  | RecordConstructor of (FStar_Ident.ident Prims.list * FStar_Ident.ident
  Prims.list) 
  | Action of FStar_Ident.lid 
  | ExceptionConstructor 
  | HasMaskedEffect 
  | Effect 
  | OnlyName 
let (uu___is_Assumption : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Assumption -> true | uu___ -> false
let (uu___is_InternalAssumption : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | InternalAssumption -> true | uu___ -> false
let (uu___is_New : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | New -> true | uu___ -> false
let (uu___is_Private : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Private -> true | uu___ -> false
let (uu___is_Unfold_for_unification_and_vcgen : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with
    | Unfold_for_unification_and_vcgen -> true
    | uu___ -> false
let (uu___is_Visible_default : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Visible_default -> true | uu___ -> false
let (uu___is_Irreducible : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Irreducible -> true | uu___ -> false
let (uu___is_Inline_for_extraction : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Inline_for_extraction -> true | uu___ -> false
let (uu___is_NoExtract : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | NoExtract -> true | uu___ -> false
let (uu___is_Noeq : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Noeq -> true | uu___ -> false
let (uu___is_Unopteq : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Unopteq -> true | uu___ -> false
let (uu___is_TotalEffect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | TotalEffect -> true | uu___ -> false
let (uu___is_Logic : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Logic -> true | uu___ -> false
let (uu___is_Reifiable : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Reifiable -> true | uu___ -> false
let (uu___is_Reflectable : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Reflectable _0 -> true | uu___ -> false
let (__proj__Reflectable__item___0 : qualifier -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Reflectable _0 -> _0
let (uu___is_Discriminator : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Discriminator _0 -> true | uu___ -> false
let (__proj__Discriminator__item___0 : qualifier -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Discriminator _0 -> _0
let (uu___is_Projector : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Projector _0 -> true | uu___ -> false
let (__proj__Projector__item___0 :
  qualifier -> (FStar_Ident.lid * FStar_Ident.ident)) =
  fun projectee -> match projectee with | Projector _0 -> _0
let (uu___is_RecordType : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | RecordType _0 -> true | uu___ -> false
let (__proj__RecordType__item___0 :
  qualifier -> (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
  = fun projectee -> match projectee with | RecordType _0 -> _0
let (uu___is_RecordConstructor : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | RecordConstructor _0 -> true | uu___ -> false
let (__proj__RecordConstructor__item___0 :
  qualifier -> (FStar_Ident.ident Prims.list * FStar_Ident.ident Prims.list))
  = fun projectee -> match projectee with | RecordConstructor _0 -> _0
let (uu___is_Action : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Action _0 -> true | uu___ -> false
let (__proj__Action__item___0 : qualifier -> FStar_Ident.lid) =
  fun projectee -> match projectee with | Action _0 -> _0
let (uu___is_ExceptionConstructor : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | ExceptionConstructor -> true | uu___ -> false
let (uu___is_HasMaskedEffect : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | HasMaskedEffect -> true | uu___ -> false
let (uu___is_Effect : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Effect -> true | uu___ -> false
let (uu___is_OnlyName : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | OnlyName -> true | uu___ -> false
type qualifiers = qualifier Prims.list
type bv_view =
  {
  bv_ppname: Prims.string ;
  bv_index: FStar_BigInt.t ;
  bv_sort: typ }
let (__proj__Mkbv_view__item__bv_ppname : bv_view -> Prims.string) =
  fun projectee ->
    match projectee with | { bv_ppname; bv_index; bv_sort;_} -> bv_ppname
let (__proj__Mkbv_view__item__bv_index : bv_view -> FStar_BigInt.t) =
  fun projectee ->
    match projectee with | { bv_ppname; bv_index; bv_sort;_} -> bv_index
let (__proj__Mkbv_view__item__bv_sort : bv_view -> typ) =
  fun projectee ->
    match projectee with | { bv_ppname; bv_index; bv_sort;_} -> bv_sort
type binder_view =
  (FStar_Syntax_Syntax.bv * (aqualv * FStar_Syntax_Syntax.term Prims.list))
type comp_view =
  | C_Total of typ 
  | C_GTotal of typ 
  | C_Lemma of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
  FStar_Syntax_Syntax.term) 
  | C_Eff of (universes * name * FStar_Syntax_Syntax.term * argv Prims.list *
  FStar_Syntax_Syntax.term Prims.list) 
let (uu___is_C_Total : comp_view -> Prims.bool) =
  fun projectee -> match projectee with | C_Total _0 -> true | uu___ -> false
let (__proj__C_Total__item___0 : comp_view -> typ) =
  fun projectee -> match projectee with | C_Total _0 -> _0
let (uu___is_C_GTotal : comp_view -> Prims.bool) =
  fun projectee ->
    match projectee with | C_GTotal _0 -> true | uu___ -> false
let (__proj__C_GTotal__item___0 : comp_view -> typ) =
  fun projectee -> match projectee with | C_GTotal _0 -> _0
let (uu___is_C_Lemma : comp_view -> Prims.bool) =
  fun projectee -> match projectee with | C_Lemma _0 -> true | uu___ -> false
let (__proj__C_Lemma__item___0 :
  comp_view ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term *
      FStar_Syntax_Syntax.term))
  = fun projectee -> match projectee with | C_Lemma _0 -> _0
let (uu___is_C_Eff : comp_view -> Prims.bool) =
  fun projectee -> match projectee with | C_Eff _0 -> true | uu___ -> false
let (__proj__C_Eff__item___0 :
  comp_view ->
    (universes * name * FStar_Syntax_Syntax.term * argv Prims.list *
      FStar_Syntax_Syntax.term Prims.list))
  = fun projectee -> match projectee with | C_Eff _0 -> _0
type ctor = (name * typ)
type lb_view =
  {
  lb_fv: FStar_Syntax_Syntax.fv ;
  lb_us: FStar_Syntax_Syntax.univ_name Prims.list ;
  lb_typ: typ ;
  lb_def: FStar_Syntax_Syntax.term }
let (__proj__Mklb_view__item__lb_fv : lb_view -> FStar_Syntax_Syntax.fv) =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_fv
let (__proj__Mklb_view__item__lb_us :
  lb_view -> FStar_Syntax_Syntax.univ_name Prims.list) =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_us
let (__proj__Mklb_view__item__lb_typ : lb_view -> typ) =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_typ
let (__proj__Mklb_view__item__lb_def : lb_view -> FStar_Syntax_Syntax.term) =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_def
type sigelt_view =
  | Sg_Let of (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) 
  | Sg_Inductive of (name * FStar_Syntax_Syntax.univ_name Prims.list *
  FStar_Syntax_Syntax.binder Prims.list * typ * ctor Prims.list) 
  | Sg_Val of (name * FStar_Syntax_Syntax.univ_name Prims.list * typ) 
  | Unk 
let (uu___is_Sg_Let : sigelt_view -> Prims.bool) =
  fun projectee -> match projectee with | Sg_Let _0 -> true | uu___ -> false
let (__proj__Sg_Let__item___0 :
  sigelt_view -> (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list)) =
  fun projectee -> match projectee with | Sg_Let _0 -> _0
let (uu___is_Sg_Inductive : sigelt_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Sg_Inductive _0 -> true | uu___ -> false
let (__proj__Sg_Inductive__item___0 :
  sigelt_view ->
    (name * FStar_Syntax_Syntax.univ_name Prims.list *
      FStar_Syntax_Syntax.binder Prims.list * typ * ctor Prims.list))
  = fun projectee -> match projectee with | Sg_Inductive _0 -> _0
let (uu___is_Sg_Val : sigelt_view -> Prims.bool) =
  fun projectee -> match projectee with | Sg_Val _0 -> true | uu___ -> false
let (__proj__Sg_Val__item___0 :
  sigelt_view -> (name * FStar_Syntax_Syntax.univ_name Prims.list * typ)) =
  fun projectee -> match projectee with | Sg_Val _0 -> _0
let (uu___is_Unk : sigelt_view -> Prims.bool) =
  fun projectee -> match projectee with | Unk -> true | uu___ -> false
type var = FStar_BigInt.t
type exp =
  | Unit 
  | Var of var 
  | Mult of (exp * exp) 
let (uu___is_Unit : exp -> Prims.bool) =
  fun projectee -> match projectee with | Unit -> true | uu___ -> false
let (uu___is_Var : exp -> Prims.bool) =
  fun projectee -> match projectee with | Var _0 -> true | uu___ -> false
let (__proj__Var__item___0 : exp -> var) =
  fun projectee -> match projectee with | Var _0 -> _0
let (uu___is_Mult : exp -> Prims.bool) =
  fun projectee -> match projectee with | Mult _0 -> true | uu___ -> false
let (__proj__Mult__item___0 : exp -> (exp * exp)) =
  fun projectee -> match projectee with | Mult _0 -> _0
type decls = FStar_Syntax_Syntax.sigelt Prims.list