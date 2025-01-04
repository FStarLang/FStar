open Prims
type name = Prims.string Prims.list
type typ = FStarC_Syntax_Syntax.term
type binders = FStarC_Syntax_Syntax.binder Prims.list
type ident = (Prims.string * FStarC_Compiler_Range_Type.range)
type univ_name = ident
type vconst =
  | C_Unit 
  | C_Int of FStarC_BigInt.t 
  | C_True 
  | C_False 
  | C_String of Prims.string 
  | C_Range of FStarC_Compiler_Range_Type.range 
  | C_Reify 
  | C_Reflect of name 
let (uu___is_C_Unit : vconst -> Prims.bool) =
  fun projectee -> match projectee with | C_Unit -> true | uu___ -> false
let (uu___is_C_Int : vconst -> Prims.bool) =
  fun projectee -> match projectee with | C_Int _0 -> true | uu___ -> false
let (__proj__C_Int__item___0 : vconst -> FStarC_BigInt.t) =
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
let (__proj__C_Range__item___0 : vconst -> FStarC_Compiler_Range_Type.range)
  = fun projectee -> match projectee with | C_Range _0 -> _0
let (uu___is_C_Reify : vconst -> Prims.bool) =
  fun projectee -> match projectee with | C_Reify -> true | uu___ -> false
let (uu___is_C_Reflect : vconst -> Prims.bool) =
  fun projectee ->
    match projectee with | C_Reflect _0 -> true | uu___ -> false
let (__proj__C_Reflect__item___0 : vconst -> name) =
  fun projectee -> match projectee with | C_Reflect _0 -> _0
type universes = FStarC_Syntax_Syntax.universe Prims.list
type pattern =
  | Pat_Constant of vconst 
  | Pat_Cons of (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.universe
  Prims.list FStar_Pervasives_Native.option * (pattern * Prims.bool)
  Prims.list) 
  | Pat_Var of (FStarC_Syntax_Syntax.bv * typ FStarC_Compiler_Sealed.sealed)
  
  | Pat_Dot_Term of FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option 
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
    (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.universe Prims.list
      FStar_Pervasives_Native.option * (pattern * Prims.bool) Prims.list))
  = fun projectee -> match projectee with | Pat_Cons _0 -> _0
let (uu___is_Pat_Var : pattern -> Prims.bool) =
  fun projectee -> match projectee with | Pat_Var _0 -> true | uu___ -> false
let (__proj__Pat_Var__item___0 :
  pattern -> (FStarC_Syntax_Syntax.bv * typ FStarC_Compiler_Sealed.sealed)) =
  fun projectee -> match projectee with | Pat_Var _0 -> _0
let (uu___is_Pat_Dot_Term : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | Pat_Dot_Term _0 -> true | uu___ -> false
let (__proj__Pat_Dot_Term__item___0 :
  pattern -> FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option) =
  fun projectee -> match projectee with | Pat_Dot_Term _0 -> _0
type branch = (pattern * FStarC_Syntax_Syntax.term)
type aqualv =
  | Q_Implicit 
  | Q_Explicit 
  | Q_Meta of FStarC_Syntax_Syntax.term 
let (uu___is_Q_Implicit : aqualv -> Prims.bool) =
  fun projectee -> match projectee with | Q_Implicit -> true | uu___ -> false
let (uu___is_Q_Explicit : aqualv -> Prims.bool) =
  fun projectee -> match projectee with | Q_Explicit -> true | uu___ -> false
let (uu___is_Q_Meta : aqualv -> Prims.bool) =
  fun projectee -> match projectee with | Q_Meta _0 -> true | uu___ -> false
let (__proj__Q_Meta__item___0 : aqualv -> FStarC_Syntax_Syntax.term) =
  fun projectee -> match projectee with | Q_Meta _0 -> _0
type argv = (FStarC_Syntax_Syntax.term * aqualv)
type ppname_t = Prims.string FStarC_Compiler_Sealed.sealed
let (as_ppname : Prims.string -> ppname_t) =
  fun x -> FStarC_Compiler_Sealed.seal x
type bv_view = {
  bv_ppname: ppname_t ;
  bv_index: FStarC_BigInt.t }
let (__proj__Mkbv_view__item__bv_ppname : bv_view -> ppname_t) =
  fun projectee ->
    match projectee with | { bv_ppname; bv_index;_} -> bv_ppname
let (__proj__Mkbv_view__item__bv_index : bv_view -> FStarC_BigInt.t) =
  fun projectee ->
    match projectee with | { bv_ppname; bv_index;_} -> bv_index
type binder_view =
  {
  binder_bv: FStarC_Syntax_Syntax.bv ;
  binder_qual: aqualv ;
  binder_attrs: FStarC_Syntax_Syntax.term Prims.list ;
  binder_sort: typ }
let (__proj__Mkbinder_view__item__binder_bv :
  binder_view -> FStarC_Syntax_Syntax.bv) =
  fun projectee ->
    match projectee with
    | { binder_bv; binder_qual; binder_attrs; binder_sort;_} -> binder_bv
let (__proj__Mkbinder_view__item__binder_qual : binder_view -> aqualv) =
  fun projectee ->
    match projectee with
    | { binder_bv; binder_qual; binder_attrs; binder_sort;_} -> binder_qual
let (__proj__Mkbinder_view__item__binder_attrs :
  binder_view -> FStarC_Syntax_Syntax.term Prims.list) =
  fun projectee ->
    match projectee with
    | { binder_bv; binder_qual; binder_attrs; binder_sort;_} -> binder_attrs
let (__proj__Mkbinder_view__item__binder_sort : binder_view -> typ) =
  fun projectee ->
    match projectee with
    | { binder_bv; binder_qual; binder_attrs; binder_sort;_} -> binder_sort
type universe_view =
  | Uv_Zero 
  | Uv_Succ of FStarC_Syntax_Syntax.universe 
  | Uv_Max of universes 
  | Uv_BVar of FStarC_BigInt.t 
  | Uv_Name of (Prims.string * FStarC_Compiler_Range_Type.range) 
  | Uv_Unif of FStarC_Syntax_Syntax.universe_uvar 
  | Uv_Unk 
let (uu___is_Uv_Zero : universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Zero -> true | uu___ -> false
let (uu___is_Uv_Succ : universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Succ _0 -> true | uu___ -> false
let (__proj__Uv_Succ__item___0 :
  universe_view -> FStarC_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Uv_Succ _0 -> _0
let (uu___is_Uv_Max : universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Max _0 -> true | uu___ -> false
let (__proj__Uv_Max__item___0 : universe_view -> universes) =
  fun projectee -> match projectee with | Uv_Max _0 -> _0
let (uu___is_Uv_BVar : universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_BVar _0 -> true | uu___ -> false
let (__proj__Uv_BVar__item___0 : universe_view -> FStarC_BigInt.t) =
  fun projectee -> match projectee with | Uv_BVar _0 -> _0
let (uu___is_Uv_Name : universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Name _0 -> true | uu___ -> false
let (__proj__Uv_Name__item___0 :
  universe_view -> (Prims.string * FStarC_Compiler_Range_Type.range)) =
  fun projectee -> match projectee with | Uv_Name _0 -> _0
let (uu___is_Uv_Unif : universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Unif _0 -> true | uu___ -> false
let (__proj__Uv_Unif__item___0 :
  universe_view -> FStarC_Syntax_Syntax.universe_uvar) =
  fun projectee -> match projectee with | Uv_Unif _0 -> _0
let (uu___is_Uv_Unk : universe_view -> Prims.bool) =
  fun projectee -> match projectee with | Uv_Unk -> true | uu___ -> false
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
  | Tv_Uvar of (FStarC_BigInt.t * FStarC_Syntax_Syntax.ctx_uvar_and_subst) 
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
let (uu___is_Tv_Var : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Var _0 -> true | uu___ -> false
let (__proj__Tv_Var__item___0 : term_view -> FStarC_Syntax_Syntax.bv) =
  fun projectee -> match projectee with | Tv_Var _0 -> _0
let (uu___is_Tv_BVar : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_BVar _0 -> true | uu___ -> false
let (__proj__Tv_BVar__item___0 : term_view -> FStarC_Syntax_Syntax.bv) =
  fun projectee -> match projectee with | Tv_BVar _0 -> _0
let (uu___is_Tv_FVar : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_FVar _0 -> true | uu___ -> false
let (__proj__Tv_FVar__item___0 : term_view -> FStarC_Syntax_Syntax.fv) =
  fun projectee -> match projectee with | Tv_FVar _0 -> _0
let (uu___is_Tv_UInst : term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_UInst _0 -> true | uu___ -> false
let (__proj__Tv_UInst__item___0 :
  term_view -> (FStarC_Syntax_Syntax.fv * universes)) =
  fun projectee -> match projectee with | Tv_UInst _0 -> _0
let (uu___is_Tv_App : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_App _0 -> true | uu___ -> false
let (__proj__Tv_App__item___0 :
  term_view -> (FStarC_Syntax_Syntax.term * argv)) =
  fun projectee -> match projectee with | Tv_App _0 -> _0
let (uu___is_Tv_Abs : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Abs _0 -> true | uu___ -> false
let (__proj__Tv_Abs__item___0 :
  term_view -> (FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.term)) =
  fun projectee -> match projectee with | Tv_Abs _0 -> _0
let (uu___is_Tv_Arrow : term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Arrow _0 -> true | uu___ -> false
let (__proj__Tv_Arrow__item___0 :
  term_view -> (FStarC_Syntax_Syntax.binder * FStarC_Syntax_Syntax.comp)) =
  fun projectee -> match projectee with | Tv_Arrow _0 -> _0
let (uu___is_Tv_Type : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Type _0 -> true | uu___ -> false
let (__proj__Tv_Type__item___0 : term_view -> FStarC_Syntax_Syntax.universe)
  = fun projectee -> match projectee with | Tv_Type _0 -> _0
let (uu___is_Tv_Refine : term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Refine _0 -> true | uu___ -> false
let (__proj__Tv_Refine__item___0 :
  term_view -> (FStarC_Syntax_Syntax.bv * typ * FStarC_Syntax_Syntax.term)) =
  fun projectee -> match projectee with | Tv_Refine _0 -> _0
let (uu___is_Tv_Const : term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Const _0 -> true | uu___ -> false
let (__proj__Tv_Const__item___0 : term_view -> vconst) =
  fun projectee -> match projectee with | Tv_Const _0 -> _0
let (uu___is_Tv_Uvar : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Uvar _0 -> true | uu___ -> false
let (__proj__Tv_Uvar__item___0 :
  term_view -> (FStarC_BigInt.t * FStarC_Syntax_Syntax.ctx_uvar_and_subst)) =
  fun projectee -> match projectee with | Tv_Uvar _0 -> _0
let (uu___is_Tv_Let : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Let _0 -> true | uu___ -> false
let (__proj__Tv_Let__item___0 :
  term_view ->
    (Prims.bool * FStarC_Syntax_Syntax.term Prims.list *
      FStarC_Syntax_Syntax.bv * typ * FStarC_Syntax_Syntax.term *
      FStarC_Syntax_Syntax.term))
  = fun projectee -> match projectee with | Tv_Let _0 -> _0
let (uu___is_Tv_Match : term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_Match _0 -> true | uu___ -> false
let (__proj__Tv_Match__item___0 :
  term_view ->
    (FStarC_Syntax_Syntax.term *
      FStarC_Syntax_Syntax.match_returns_ascription
      FStar_Pervasives_Native.option * branch Prims.list))
  = fun projectee -> match projectee with | Tv_Match _0 -> _0
let (uu___is_Tv_AscribedT : term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_AscribedT _0 -> true | uu___ -> false
let (__proj__Tv_AscribedT__item___0 :
  term_view ->
    (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term *
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option * Prims.bool))
  = fun projectee -> match projectee with | Tv_AscribedT _0 -> _0
let (uu___is_Tv_AscribedC : term_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Tv_AscribedC _0 -> true | uu___ -> false
let (__proj__Tv_AscribedC__item___0 :
  term_view ->
    (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.comp *
      FStarC_Syntax_Syntax.term FStar_Pervasives_Native.option * Prims.bool))
  = fun projectee -> match projectee with | Tv_AscribedC _0 -> _0
let (uu___is_Tv_Unknown : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Unknown -> true | uu___ -> false
let (uu___is_Tv_Unsupp : term_view -> Prims.bool) =
  fun projectee -> match projectee with | Tv_Unsupp -> true | uu___ -> false
let (notAscription : term_view -> Prims.bool) =
  fun tv ->
    (Prims.op_Negation (uu___is_Tv_AscribedT tv)) &&
      (Prims.op_Negation (uu___is_Tv_AscribedC tv))
type comp_view =
  | C_Total of typ 
  | C_GTotal of typ 
  | C_Lemma of (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term *
  FStarC_Syntax_Syntax.term) 
  | C_Eff of (universes * name * FStarC_Syntax_Syntax.term * argv Prims.list
  * FStarC_Syntax_Syntax.term Prims.list) 
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
    (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.term *
      FStarC_Syntax_Syntax.term))
  = fun projectee -> match projectee with | C_Lemma _0 -> _0
let (uu___is_C_Eff : comp_view -> Prims.bool) =
  fun projectee -> match projectee with | C_Eff _0 -> true | uu___ -> false
let (__proj__C_Eff__item___0 :
  comp_view ->
    (universes * name * FStarC_Syntax_Syntax.term * argv Prims.list *
      FStarC_Syntax_Syntax.term Prims.list))
  = fun projectee -> match projectee with | C_Eff _0 -> _0
type ctor = (name * typ)
type lb_view =
  {
  lb_fv: FStarC_Syntax_Syntax.fv ;
  lb_us: univ_name Prims.list ;
  lb_typ: typ ;
  lb_def: FStarC_Syntax_Syntax.term }
let (__proj__Mklb_view__item__lb_fv : lb_view -> FStarC_Syntax_Syntax.fv) =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_fv
let (__proj__Mklb_view__item__lb_us : lb_view -> univ_name Prims.list) =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_us
let (__proj__Mklb_view__item__lb_typ : lb_view -> typ) =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_typ
let (__proj__Mklb_view__item__lb_def : lb_view -> FStarC_Syntax_Syntax.term)
  =
  fun projectee ->
    match projectee with | { lb_fv; lb_us; lb_typ; lb_def;_} -> lb_def
type sigelt_view =
  | Sg_Let of (Prims.bool * FStarC_Syntax_Syntax.letbinding Prims.list) 
  | Sg_Inductive of (name * univ_name Prims.list *
  FStarC_Syntax_Syntax.binder Prims.list * typ * ctor Prims.list) 
  | Sg_Val of (name * univ_name Prims.list * typ) 
  | Unk 
let (uu___is_Sg_Let : sigelt_view -> Prims.bool) =
  fun projectee -> match projectee with | Sg_Let _0 -> true | uu___ -> false
let (__proj__Sg_Let__item___0 :
  sigelt_view -> (Prims.bool * FStarC_Syntax_Syntax.letbinding Prims.list)) =
  fun projectee -> match projectee with | Sg_Let _0 -> _0
let (uu___is_Sg_Inductive : sigelt_view -> Prims.bool) =
  fun projectee ->
    match projectee with | Sg_Inductive _0 -> true | uu___ -> false
let (__proj__Sg_Inductive__item___0 :
  sigelt_view ->
    (name * univ_name Prims.list * FStarC_Syntax_Syntax.binder Prims.list *
      typ * ctor Prims.list))
  = fun projectee -> match projectee with | Sg_Inductive _0 -> _0
let (uu___is_Sg_Val : sigelt_view -> Prims.bool) =
  fun projectee -> match projectee with | Sg_Val _0 -> true | uu___ -> false
let (__proj__Sg_Val__item___0 :
  sigelt_view -> (name * univ_name Prims.list * typ)) =
  fun projectee -> match projectee with | Sg_Val _0 -> _0
let (uu___is_Unk : sigelt_view -> Prims.bool) =
  fun projectee -> match projectee with | Unk -> true | uu___ -> false
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
let (__proj__Reflectable__item___0 : qualifier -> name) =
  fun projectee -> match projectee with | Reflectable _0 -> _0
let (uu___is_Discriminator : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Discriminator _0 -> true | uu___ -> false
let (__proj__Discriminator__item___0 : qualifier -> name) =
  fun projectee -> match projectee with | Discriminator _0 -> _0
let (uu___is_Projector : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | Projector _0 -> true | uu___ -> false
let (__proj__Projector__item___0 : qualifier -> (name * ident)) =
  fun projectee -> match projectee with | Projector _0 -> _0
let (uu___is_RecordType : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | RecordType _0 -> true | uu___ -> false
let (__proj__RecordType__item___0 :
  qualifier -> (ident Prims.list * ident Prims.list)) =
  fun projectee -> match projectee with | RecordType _0 -> _0
let (uu___is_RecordConstructor : qualifier -> Prims.bool) =
  fun projectee ->
    match projectee with | RecordConstructor _0 -> true | uu___ -> false
let (__proj__RecordConstructor__item___0 :
  qualifier -> (ident Prims.list * ident Prims.list)) =
  fun projectee -> match projectee with | RecordConstructor _0 -> _0
let (uu___is_Action : qualifier -> Prims.bool) =
  fun projectee -> match projectee with | Action _0 -> true | uu___ -> false
let (__proj__Action__item___0 : qualifier -> name) =
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
type var = FStarC_BigInt.t
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
type decls = FStarC_Syntax_Syntax.sigelt Prims.list