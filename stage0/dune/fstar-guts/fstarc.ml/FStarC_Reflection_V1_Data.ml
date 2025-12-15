open Prims
type name = Prims.string Prims.list
type typ = FStarC_Syntax_Syntax.term
type binders = FStarC_Syntax_Syntax.binder Prims.list
type ident = (Prims.string * FStarC_Range_Type.t)
type univ_name = ident
type vconst =
  | C_Unit 
  | C_Int of Prims.int 
  | C_True 
  | C_False 
  | C_String of Prims.string 
  | C_Range of FStarC_Range_Type.t 
  | C_Reify 
  | C_Reflect of name 
let uu___is_C_Unit (projectee : vconst) : Prims.bool=
  match projectee with | C_Unit -> true | uu___ -> false
let uu___is_C_Int (projectee : vconst) : Prims.bool=
  match projectee with | C_Int _0 -> true | uu___ -> false
let __proj__C_Int__item___0 (projectee : vconst) : Prims.int=
  match projectee with | C_Int _0 -> _0
let uu___is_C_True (projectee : vconst) : Prims.bool=
  match projectee with | C_True -> true | uu___ -> false
let uu___is_C_False (projectee : vconst) : Prims.bool=
  match projectee with | C_False -> true | uu___ -> false
let uu___is_C_String (projectee : vconst) : Prims.bool=
  match projectee with | C_String _0 -> true | uu___ -> false
let __proj__C_String__item___0 (projectee : vconst) : Prims.string=
  match projectee with | C_String _0 -> _0
let uu___is_C_Range (projectee : vconst) : Prims.bool=
  match projectee with | C_Range _0 -> true | uu___ -> false
let __proj__C_Range__item___0 (projectee : vconst) : FStarC_Range_Type.t=
  match projectee with | C_Range _0 -> _0
let uu___is_C_Reify (projectee : vconst) : Prims.bool=
  match projectee with | C_Reify -> true | uu___ -> false
let uu___is_C_Reflect (projectee : vconst) : Prims.bool=
  match projectee with | C_Reflect _0 -> true | uu___ -> false
let __proj__C_Reflect__item___0 (projectee : vconst) : name=
  match projectee with | C_Reflect _0 -> _0
type universes = FStarC_Syntax_Syntax.universe Prims.list
type pattern =
  | Pat_Constant of vconst 
  | Pat_Cons of (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.universe
  Prims.list FStar_Pervasives_Native.option * (pattern * Prims.bool)
  Prims.list) 
  | Pat_Var of (FStarC_Syntax_Syntax.bv * typ FStarC_Sealed.sealed) 
  | Pat_Dot_Term of FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option 
let uu___is_Pat_Constant (projectee : pattern) : Prims.bool=
  match projectee with | Pat_Constant _0 -> true | uu___ -> false
let __proj__Pat_Constant__item___0 (projectee : pattern) : vconst=
  match projectee with | Pat_Constant _0 -> _0
let uu___is_Pat_Cons (projectee : pattern) : Prims.bool=
  match projectee with | Pat_Cons _0 -> true | uu___ -> false
let __proj__Pat_Cons__item___0 (projectee : pattern) :
  (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.universe Prims.list
    FStar_Pervasives_Native.option * (pattern * Prims.bool) Prims.list)=
  match projectee with | Pat_Cons _0 -> _0
let uu___is_Pat_Var (projectee : pattern) : Prims.bool=
  match projectee with | Pat_Var _0 -> true | uu___ -> false
let __proj__Pat_Var__item___0 (projectee : pattern) :
  (FStarC_Syntax_Syntax.bv * typ FStarC_Sealed.sealed)=
  match projectee with | Pat_Var _0 -> _0
let uu___is_Pat_Dot_Term (projectee : pattern) : Prims.bool=
  match projectee with | Pat_Dot_Term _0 -> true | uu___ -> false
let __proj__Pat_Dot_Term__item___0 (projectee : pattern) :
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option=
  match projectee with | Pat_Dot_Term _0 -> _0
type branch = (pattern * FStarC_Syntax_Syntax.term)
type aqualv =
  | Q_Implicit 
  | Q_Explicit 
  | Q_Meta of FStarC_Syntax_Syntax.term 
let uu___is_Q_Implicit (projectee : aqualv) : Prims.bool=
  match projectee with | Q_Implicit -> true | uu___ -> false
let uu___is_Q_Explicit (projectee : aqualv) : Prims.bool=
  match projectee with | Q_Explicit -> true | uu___ -> false
let uu___is_Q_Meta (projectee : aqualv) : Prims.bool=
  match projectee with | Q_Meta _0 -> true | uu___ -> false
let __proj__Q_Meta__item___0 (projectee : aqualv) :
  FStarC_Syntax_Syntax.term= match projectee with | Q_Meta _0 -> _0
type argv = (FStarC_Syntax_Syntax.term * aqualv)
type ppname_t = Prims.string FStarC_Sealed.sealed
let as_ppname (x : Prims.string) : ppname_t= FStarC_Sealed.seal x
type bv_view = {
  bv_ppname: ppname_t ;
  bv_index: Prims.int }
let __proj__Mkbv_view__item__bv_ppname (projectee : bv_view) : ppname_t=
  match projectee with | { bv_ppname; bv_index;_} -> bv_ppname
let __proj__Mkbv_view__item__bv_index (projectee : bv_view) : Prims.int=
  match projectee with | { bv_ppname; bv_index;_} -> bv_index
type binder_view =
  {
  binder_bv: FStarC_Syntax_Syntax.bv ;
  binder_qual: aqualv ;
  binder_attrs: FStarC_Syntax_Syntax.term Prims.list ;
  binder_sort: typ }
let __proj__Mkbinder_view__item__binder_bv (projectee : binder_view) :
  FStarC_Syntax_Syntax.bv=
  match projectee with
  | { binder_bv; binder_qual; binder_attrs; binder_sort;_} -> binder_bv
let __proj__Mkbinder_view__item__binder_qual (projectee : binder_view) :
  aqualv=
  match projectee with
  | { binder_bv; binder_qual; binder_attrs; binder_sort;_} -> binder_qual
let __proj__Mkbinder_view__item__binder_attrs (projectee : binder_view) :
  FStarC_Syntax_Syntax.term Prims.list=
  match projectee with
  | { binder_bv; binder_qual; binder_attrs; binder_sort;_} -> binder_attrs
let __proj__Mkbinder_view__item__binder_sort (projectee : binder_view) : 
  typ=
  match projectee with
  | { binder_bv; binder_qual; binder_attrs; binder_sort;_} -> binder_sort
type universe_view =
  | Uv_Zero 
  | Uv_Succ of FStarC_Syntax_Syntax.universe 
  | Uv_Max of universes 
  | Uv_BVar of Prims.int 
  | Uv_Name of (Prims.string * FStarC_Range_Type.t) 
  | Uv_Unif of FStarC_Syntax_Syntax.universe_uvar 
  | Uv_Unk 
let uu___is_Uv_Zero (projectee : universe_view) : Prims.bool=
  match projectee with | Uv_Zero -> true | uu___ -> false
let uu___is_Uv_Succ (projectee : universe_view) : Prims.bool=
  match projectee with | Uv_Succ _0 -> true | uu___ -> false
let __proj__Uv_Succ__item___0 (projectee : universe_view) :
  FStarC_Syntax_Syntax.universe= match projectee with | Uv_Succ _0 -> _0
let uu___is_Uv_Max (projectee : universe_view) : Prims.bool=
  match projectee with | Uv_Max _0 -> true | uu___ -> false
let __proj__Uv_Max__item___0 (projectee : universe_view) : universes=
  match projectee with | Uv_Max _0 -> _0
let uu___is_Uv_BVar (projectee : universe_view) : Prims.bool=
  match projectee with | Uv_BVar _0 -> true | uu___ -> false
let __proj__Uv_BVar__item___0 (projectee : universe_view) : Prims.int=
  match projectee with | Uv_BVar _0 -> _0
let uu___is_Uv_Name (projectee : universe_view) : Prims.bool=
  match projectee with | Uv_Name _0 -> true | uu___ -> false
let __proj__Uv_Name__item___0 (projectee : universe_view) :
  (Prims.string * FStarC_Range_Type.t)=
  match projectee with | Uv_Name _0 -> _0
let uu___is_Uv_Unif (projectee : universe_view) : Prims.bool=
  match projectee with | Uv_Unif _0 -> true | uu___ -> false
let __proj__Uv_Unif__item___0 (projectee : universe_view) :
  FStarC_Syntax_Syntax.universe_uvar= match projectee with | Uv_Unif _0 -> _0
let uu___is_Uv_Unk (projectee : universe_view) : Prims.bool=
  match projectee with | Uv_Unk -> true | uu___ -> false
type term_view =
  | Tv_Var of FStarC_Syntax_Syntax.bv 
  | Tv_BVar of FStarC_Syntax_Syntax.bv 
  | Tv_FVar of FStarC_Syntax_Syntax.fv 
  | Tv_UInst of (FStarC_Syntax_Syntax.fv * universes) 
  | Tv_App of (FStarC_Syntax_Syntax.term * argv) 
  | Tv_Abs of (FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.term) 
  | Tv_Arrow of (FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.comp) 
  | Tv_Type of FStarC_Syntax_Syntax.universe 
  | Tv_Refine of (FStarC_Syntax_Syntax.bv * typ * FStarC_Syntax_Syntax.term)
  
  | Tv_Const of vconst 
  | Tv_Uvar of (Prims.int * FStarC_Syntax_Syntax.ctx_uvar_and_subst) 
  | Tv_Let of (Prims.bool * FStarC_Syntax_Syntax.term Prims.list *
  FStarC_Syntax_Syntax.bv * typ * FStarC_Syntax_Syntax.term *
  FStarC_Syntax_Syntax.term) 
  | Tv_Match of (FStarC_Syntax_Syntax.term *
  FStarC_Syntax_Syntax.match_returns_ascription
  FStar_Pervasives_Native.option * branch Prims.list) 
  | Tv_AscribedT of (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term *
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option * Prims.bool) 
  | Tv_AscribedC of (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.comp *
  FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option * Prims.bool) 
  | Tv_Unknown 
  | Tv_Unsupp 
let uu___is_Tv_Var (projectee : term_view) : Prims.bool=
  match projectee with | Tv_Var _0 -> true | uu___ -> false
let __proj__Tv_Var__item___0 (projectee : term_view) :
  FStarC_Syntax_Syntax.bv= match projectee with | Tv_Var _0 -> _0
let uu___is_Tv_BVar (projectee : term_view) : Prims.bool=
  match projectee with | Tv_BVar _0 -> true | uu___ -> false
let __proj__Tv_BVar__item___0 (projectee : term_view) :
  FStarC_Syntax_Syntax.bv= match projectee with | Tv_BVar _0 -> _0
let uu___is_Tv_FVar (projectee : term_view) : Prims.bool=
  match projectee with | Tv_FVar _0 -> true | uu___ -> false
let __proj__Tv_FVar__item___0 (projectee : term_view) :
  FStarC_Syntax_Syntax.fv= match projectee with | Tv_FVar _0 -> _0
let uu___is_Tv_UInst (projectee : term_view) : Prims.bool=
  match projectee with | Tv_UInst _0 -> true | uu___ -> false
let __proj__Tv_UInst__item___0 (projectee : term_view) :
  (FStarC_Syntax_Syntax.fv * universes)=
  match projectee with | Tv_UInst _0 -> _0
let uu___is_Tv_App (projectee : term_view) : Prims.bool=
  match projectee with | Tv_App _0 -> true | uu___ -> false
let __proj__Tv_App__item___0 (projectee : term_view) :
  (FStarC_Syntax_Syntax.term * argv)= match projectee with | Tv_App _0 -> _0
let uu___is_Tv_Abs (projectee : term_view) : Prims.bool=
  match projectee with | Tv_Abs _0 -> true | uu___ -> false
let __proj__Tv_Abs__item___0 (projectee : term_view) :
  (FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.term)=
  match projectee with | Tv_Abs _0 -> _0
let uu___is_Tv_Arrow (projectee : term_view) : Prims.bool=
  match projectee with | Tv_Arrow _0 -> true | uu___ -> false
let __proj__Tv_Arrow__item___0 (projectee : term_view) :
  (FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.comp)=
  match projectee with | Tv_Arrow _0 -> _0
let uu___is_Tv_Type (projectee : term_view) : Prims.bool=
  match projectee with | Tv_Type _0 -> true | uu___ -> false
let __proj__Tv_Type__item___0 (projectee : term_view) :
  FStarC_Syntax_Syntax.universe= match projectee with | Tv_Type _0 -> _0
let uu___is_Tv_Refine (projectee : term_view) : Prims.bool=
  match projectee with | Tv_Refine _0 -> true | uu___ -> false
let __proj__Tv_Refine__item___0 (projectee : term_view) :
  (FStarC_Syntax_Syntax.bv * typ * FStarC_Syntax_Syntax.term)=
  match projectee with | Tv_Refine _0 -> _0
let uu___is_Tv_Const (projectee : term_view) : Prims.bool=
  match projectee with | Tv_Const _0 -> true | uu___ -> false
let __proj__Tv_Const__item___0 (projectee : term_view) : vconst=
  match projectee with | Tv_Const _0 -> _0
let uu___is_Tv_Uvar (projectee : term_view) : Prims.bool=
  match projectee with | Tv_Uvar _0 -> true | uu___ -> false
let __proj__Tv_Uvar__item___0 (projectee : term_view) :
  (Prims.int * FStarC_Syntax_Syntax.ctx_uvar_and_subst)=
  match projectee with | Tv_Uvar _0 -> _0
let uu___is_Tv_Let (projectee : term_view) : Prims.bool=
  match projectee with | Tv_Let _0 -> true | uu___ -> false
let __proj__Tv_Let__item___0 (projectee : term_view) :
  (Prims.bool * FStarC_Syntax_Syntax.term Prims.list *
    FStarC_Syntax_Syntax.bv * typ * FStarC_Syntax_Syntax.term *
    FStarC_Syntax_Syntax.term)=
  match projectee with | Tv_Let _0 -> _0
let uu___is_Tv_Match (projectee : term_view) : Prims.bool=
  match projectee with | Tv_Match _0 -> true | uu___ -> false
let __proj__Tv_Match__item___0 (projectee : term_view) :
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.match_returns_ascription
    FStar_Pervasives_Native.option * branch Prims.list)=
  match projectee with | Tv_Match _0 -> _0
let uu___is_Tv_AscribedT (projectee : term_view) : Prims.bool=
  match projectee with | Tv_AscribedT _0 -> true | uu___ -> false
let __proj__Tv_AscribedT__item___0 (projectee : term_view) :
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term *
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option * Prims.bool)=
  match projectee with | Tv_AscribedT _0 -> _0
let uu___is_Tv_AscribedC (projectee : term_view) : Prims.bool=
  match projectee with | Tv_AscribedC _0 -> true | uu___ -> false
let __proj__Tv_AscribedC__item___0 (projectee : term_view) :
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.comp *
    FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option * Prims.bool)=
  match projectee with | Tv_AscribedC _0 -> _0
let uu___is_Tv_Unknown (projectee : term_view) : Prims.bool=
  match projectee with | Tv_Unknown -> true | uu___ -> false
let uu___is_Tv_Unsupp (projectee : term_view) : Prims.bool=
  match projectee with | Tv_Unsupp -> true | uu___ -> false
let notAscription (tv : term_view) : Prims.bool=
  (Prims.op_Negation (uu___is_Tv_AscribedT tv)) &&
    (Prims.op_Negation (uu___is_Tv_AscribedC tv))
type comp_view =
  | C_Total of typ 
  | C_GTotal of typ 
  | C_Lemma of (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term *
  FStarC_Syntax_Syntax.term) 
  | C_Eff of (universes * name * FStarC_Syntax_Syntax.term * argv Prims.list
  * FStarC_Syntax_Syntax.term Prims.list) 
let uu___is_C_Total (projectee : comp_view) : Prims.bool=
  match projectee with | C_Total _0 -> true | uu___ -> false
let __proj__C_Total__item___0 (projectee : comp_view) : typ=
  match projectee with | C_Total _0 -> _0
let uu___is_C_GTotal (projectee : comp_view) : Prims.bool=
  match projectee with | C_GTotal _0 -> true | uu___ -> false
let __proj__C_GTotal__item___0 (projectee : comp_view) : typ=
  match projectee with | C_GTotal _0 -> _0
let uu___is_C_Lemma (projectee : comp_view) : Prims.bool=
  match projectee with | C_Lemma _0 -> true | uu___ -> false
let __proj__C_Lemma__item___0 (projectee : comp_view) :
  (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term *
    FStarC_Syntax_Syntax.term)=
  match projectee with | C_Lemma _0 -> _0
let uu___is_C_Eff (projectee : comp_view) : Prims.bool=
  match projectee with | C_Eff _0 -> true | uu___ -> false
let __proj__C_Eff__item___0 (projectee : comp_view) :
  (universes * name * FStarC_Syntax_Syntax.term * argv Prims.list *
    FStarC_Syntax_Syntax.term Prims.list)=
  match projectee with | C_Eff _0 -> _0
type ctor = (name * typ)
type lb_view =
  {
  lb_fv: FStarC_Syntax_Syntax.fv ;
  lb_us: univ_name Prims.list ;
  lb_typ: typ ;
  lb_def: FStarC_Syntax_Syntax.term }
let __proj__Mklb_view__item__lb_fv (projectee : lb_view) :
  FStarC_Syntax_Syntax.fv=
  match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_fv
let __proj__Mklb_view__item__lb_us (projectee : lb_view) :
  univ_name Prims.list=
  match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_us
let __proj__Mklb_view__item__lb_typ (projectee : lb_view) : typ=
  match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_typ
let __proj__Mklb_view__item__lb_def (projectee : lb_view) :
  FStarC_Syntax_Syntax.term=
  match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_def
type sigelt_view =
  | Sg_Let of (Prims.bool * FStarC_Syntax_Syntax.letbinding Prims.list) 
  | Sg_Inductive of (name * univ_name Prims.list *
  FStarC_Syntax_Syntax.binder Prims.list * typ * ctor Prims.list) 
  | Sg_Val of (name * univ_name Prims.list * typ) 
  | Unk 
let uu___is_Sg_Let (projectee : sigelt_view) : Prims.bool=
  match projectee with | Sg_Let _0 -> true | uu___ -> false
let __proj__Sg_Let__item___0 (projectee : sigelt_view) :
  (Prims.bool * FStarC_Syntax_Syntax.letbinding Prims.list)=
  match projectee with | Sg_Let _0 -> _0
let uu___is_Sg_Inductive (projectee : sigelt_view) : Prims.bool=
  match projectee with | Sg_Inductive _0 -> true | uu___ -> false
let __proj__Sg_Inductive__item___0 (projectee : sigelt_view) :
  (name * univ_name Prims.list * FStarC_Syntax_Syntax.binder Prims.list * typ
    * ctor Prims.list)=
  match projectee with | Sg_Inductive _0 -> _0
let uu___is_Sg_Val (projectee : sigelt_view) : Prims.bool=
  match projectee with | Sg_Val _0 -> true | uu___ -> false
let __proj__Sg_Val__item___0 (projectee : sigelt_view) :
  (name * univ_name Prims.list * typ)= match projectee with | Sg_Val _0 -> _0
let uu___is_Unk (projectee : sigelt_view) : Prims.bool=
  match projectee with | Unk -> true | uu___ -> false
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
  | Reflectable of name 
  | Discriminator of name 
  | Projector of (name * ident) 
  | RecordType of (ident Prims.list * ident Prims.list) 
  | RecordConstructor of (ident Prims.list * ident Prims.list) 
  | Action of name 
  | ExceptionConstructor 
  | HasMaskedEffect 
  | Effect 
  | OnlyName 
let uu___is_Assumption (projectee : qualifier) : Prims.bool=
  match projectee with | Assumption -> true | uu___ -> false
let uu___is_InternalAssumption (projectee : qualifier) : Prims.bool=
  match projectee with | InternalAssumption -> true | uu___ -> false
let uu___is_New (projectee : qualifier) : Prims.bool=
  match projectee with | New -> true | uu___ -> false
let uu___is_Private (projectee : qualifier) : Prims.bool=
  match projectee with | Private -> true | uu___ -> false
let uu___is_Unfold_for_unification_and_vcgen (projectee : qualifier) :
  Prims.bool=
  match projectee with
  | Unfold_for_unification_and_vcgen -> true
  | uu___ -> false
let uu___is_Visible_default (projectee : qualifier) : Prims.bool=
  match projectee with | Visible_default -> true | uu___ -> false
let uu___is_Irreducible (projectee : qualifier) : Prims.bool=
  match projectee with | Irreducible -> true | uu___ -> false
let uu___is_Inline_for_extraction (projectee : qualifier) : Prims.bool=
  match projectee with | Inline_for_extraction -> true | uu___ -> false
let uu___is_NoExtract (projectee : qualifier) : Prims.bool=
  match projectee with | NoExtract -> true | uu___ -> false
let uu___is_Noeq (projectee : qualifier) : Prims.bool=
  match projectee with | Noeq -> true | uu___ -> false
let uu___is_Unopteq (projectee : qualifier) : Prims.bool=
  match projectee with | Unopteq -> true | uu___ -> false
let uu___is_TotalEffect (projectee : qualifier) : Prims.bool=
  match projectee with | TotalEffect -> true | uu___ -> false
let uu___is_Logic (projectee : qualifier) : Prims.bool=
  match projectee with | Logic -> true | uu___ -> false
let uu___is_Reifiable (projectee : qualifier) : Prims.bool=
  match projectee with | Reifiable -> true | uu___ -> false
let uu___is_Reflectable (projectee : qualifier) : Prims.bool=
  match projectee with | Reflectable _0 -> true | uu___ -> false
let __proj__Reflectable__item___0 (projectee : qualifier) : name=
  match projectee with | Reflectable _0 -> _0
let uu___is_Discriminator (projectee : qualifier) : Prims.bool=
  match projectee with | Discriminator _0 -> true | uu___ -> false
let __proj__Discriminator__item___0 (projectee : qualifier) : name=
  match projectee with | Discriminator _0 -> _0
let uu___is_Projector (projectee : qualifier) : Prims.bool=
  match projectee with | Projector _0 -> true | uu___ -> false
let __proj__Projector__item___0 (projectee : qualifier) : (name * ident)=
  match projectee with | Projector _0 -> _0
let uu___is_RecordType (projectee : qualifier) : Prims.bool=
  match projectee with | RecordType _0 -> true | uu___ -> false
let __proj__RecordType__item___0 (projectee : qualifier) :
  (ident Prims.list * ident Prims.list)=
  match projectee with | RecordType _0 -> _0
let uu___is_RecordConstructor (projectee : qualifier) : Prims.bool=
  match projectee with | RecordConstructor _0 -> true | uu___ -> false
let __proj__RecordConstructor__item___0 (projectee : qualifier) :
  (ident Prims.list * ident Prims.list)=
  match projectee with | RecordConstructor _0 -> _0
let uu___is_Action (projectee : qualifier) : Prims.bool=
  match projectee with | Action _0 -> true | uu___ -> false
let __proj__Action__item___0 (projectee : qualifier) : name=
  match projectee with | Action _0 -> _0
let uu___is_ExceptionConstructor (projectee : qualifier) : Prims.bool=
  match projectee with | ExceptionConstructor -> true | uu___ -> false
let uu___is_HasMaskedEffect (projectee : qualifier) : Prims.bool=
  match projectee with | HasMaskedEffect -> true | uu___ -> false
let uu___is_Effect (projectee : qualifier) : Prims.bool=
  match projectee with | Effect -> true | uu___ -> false
let uu___is_OnlyName (projectee : qualifier) : Prims.bool=
  match projectee with | OnlyName -> true | uu___ -> false
type qualifiers = qualifier Prims.list
type var = Prims.int
type exp =
  | Unit 
  | Var of var 
  | Mult of (exp * exp) 
let uu___is_Unit (projectee : exp) : Prims.bool=
  match projectee with | Unit -> true | uu___ -> false
let uu___is_Var (projectee : exp) : Prims.bool=
  match projectee with | Var _0 -> true | uu___ -> false
let __proj__Var__item___0 (projectee : exp) : var=
  match projectee with | Var _0 -> _0
let uu___is_Mult (projectee : exp) : Prims.bool=
  match projectee with | Mult _0 -> true | uu___ -> false
let __proj__Mult__item___0 (projectee : exp) : (exp * exp)=
  match projectee with | Mult _0 -> _0
type decls = FStarC_Syntax_Syntax.sigelt Prims.list
