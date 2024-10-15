open Prims
let (interleave_hack : Prims.int) = (Prims.of_int (123))
type var = FStarC_Syntax_Syntax.bv
type sort = Prims.int
type constant =
  | Unit 
  | Bool of Prims.bool 
  | Int of FStarC_BigInt.t 
  | String of (Prims.string * FStarC_Compiler_Range_Type.range) 
  | Char of FStar_Char.char 
  | Range of FStarC_Compiler_Range_Type.range 
  | SConst of FStarC_Const.sconst 
  | Real of Prims.string 
let (uu___is_Unit : constant -> Prims.bool) =
  fun projectee -> match projectee with | Unit -> true | uu___ -> false
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> true | uu___ -> false
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> _0
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee -> match projectee with | Int _0 -> true | uu___ -> false
let (__proj__Int__item___0 : constant -> FStarC_BigInt.t) =
  fun projectee -> match projectee with | Int _0 -> _0
let (uu___is_String : constant -> Prims.bool) =
  fun projectee -> match projectee with | String _0 -> true | uu___ -> false
let (__proj__String__item___0 :
  constant -> (Prims.string * FStarC_Compiler_Range_Type.range)) =
  fun projectee -> match projectee with | String _0 -> _0
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee -> match projectee with | Char _0 -> true | uu___ -> false
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee -> match projectee with | Char _0 -> _0
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee -> match projectee with | Range _0 -> true | uu___ -> false
let (__proj__Range__item___0 : constant -> FStarC_Compiler_Range_Type.range)
  = fun projectee -> match projectee with | Range _0 -> _0
let (uu___is_SConst : constant -> Prims.bool) =
  fun projectee -> match projectee with | SConst _0 -> true | uu___ -> false
let (__proj__SConst__item___0 : constant -> FStarC_Const.sconst) =
  fun projectee -> match projectee with | SConst _0 -> _0
let (uu___is_Real : constant -> Prims.bool) =
  fun projectee -> match projectee with | Real _0 -> true | uu___ -> false
let (__proj__Real__item___0 : constant -> Prims.string) =
  fun projectee -> match projectee with | Real _0 -> _0
type atom =
  | Var of var 
  | Match of (t *
  (unit ->
     FStarC_Syntax_Syntax.match_returns_ascription
       FStar_Pervasives_Native.option)
  * (unit -> FStarC_Syntax_Syntax.branch Prims.list) *
  (unit -> FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  
  | UnreducedLet of (var * t FStarC_Thunk.t * t FStarC_Thunk.t * t
  FStarC_Thunk.t * FStarC_Syntax_Syntax.letbinding) 
  | UnreducedLetRec of ((var * t * t) Prims.list * t *
  FStarC_Syntax_Syntax.letbinding Prims.list) 
  | UVar of FStarC_Syntax_Syntax.term FStarC_Thunk.t 
and lam_shape =
  | Lam_bs of (t Prims.list * FStarC_Syntax_Syntax.binders *
  FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option) 
  | Lam_args of (t * FStarC_Syntax_Syntax.aqual) Prims.list 
  | Lam_primop of (FStarC_Syntax_Syntax.fv * (t * FStarC_Syntax_Syntax.aqual)
  Prims.list) 
and t'__Lam__payload =
  {
  interp: (t * FStarC_Syntax_Syntax.aqual) Prims.list -> t ;
  shape: lam_shape ;
  arity: Prims.int }
and t' =
  | Lam of t'__Lam__payload 
  | Accu of (atom * (t * FStarC_Syntax_Syntax.aqual) Prims.list) 
  | Construct of (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.universe
  Prims.list * (t * FStarC_Syntax_Syntax.aqual) Prims.list) 
  | FV of (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.universe Prims.list
  * (t * FStarC_Syntax_Syntax.aqual) Prims.list) 
  | Constant of constant 
  | Type_t of FStarC_Syntax_Syntax.universe 
  | Univ of FStarC_Syntax_Syntax.universe 
  | Unknown 
  | Arrow of (FStarC_Syntax_Syntax.term FStarC_Thunk.t,
  ((t * FStarC_Syntax_Syntax.aqual) Prims.list * comp))
  FStar_Pervasives.either 
  | Refinement of ((t -> t) * (unit -> (t * FStarC_Syntax_Syntax.aqual))) 
  | Reflect of t 
  | Quote of (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.quoteinfo) 
  | Lazy of ((FStarC_Syntax_Syntax.lazyinfo,
  (FStarC_Dyn.dyn * FStarC_Syntax_Syntax.emb_typ)) FStar_Pervasives.either *
  t FStarC_Thunk.t) 
  | Meta of (t * FStarC_Syntax_Syntax.metadata FStarC_Thunk.t) 
  | TopLevelLet of (FStarC_Syntax_Syntax.letbinding * Prims.int * (t *
  FStarC_Syntax_Syntax.aqual) Prims.list) 
  | TopLevelRec of (FStarC_Syntax_Syntax.letbinding * Prims.int * Prims.bool
  Prims.list * (t * FStarC_Syntax_Syntax.aqual) Prims.list) 
  | LocalLetRec of (Prims.int * FStarC_Syntax_Syntax.letbinding *
  FStarC_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
  FStarC_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool Prims.list) 
and t = {
  nbe_t: t' ;
  nbe_r: FStarC_Compiler_Range_Type.range }
and comp =
  | Tot of t 
  | GTot of t 
  | Comp of comp_typ 
and comp_typ =
  {
  comp_univs: FStarC_Syntax_Syntax.universes ;
  effect_name: FStarC_Ident.lident ;
  result_typ: t ;
  effect_args: (t * FStarC_Syntax_Syntax.aqual) Prims.list ;
  flags: cflag Prims.list }
and residual_comp =
  {
  residual_effect: FStarC_Ident.lident ;
  residual_typ: t FStar_Pervasives_Native.option ;
  residual_flags: cflag Prims.list }
and cflag =
  | TOTAL 
  | MLEFFECT 
  | RETURN 
  | PARTIAL_RETURN 
  | SOMETRIVIAL 
  | TRIVIAL_POSTCONDITION 
  | SHOULD_NOT_INLINE 
  | LEMMA 
  | CPS 
  | DECREASES_lex of t Prims.list 
  | DECREASES_wf of (t * t) 
let (uu___is_Var : atom -> Prims.bool) =
  fun projectee -> match projectee with | Var _0 -> true | uu___ -> false
let (__proj__Var__item___0 : atom -> var) =
  fun projectee -> match projectee with | Var _0 -> _0
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee -> match projectee with | Match _0 -> true | uu___ -> false
let (__proj__Match__item___0 :
  atom ->
    (t *
      (unit ->
         FStarC_Syntax_Syntax.match_returns_ascription
           FStar_Pervasives_Native.option)
      * (unit -> FStarC_Syntax_Syntax.branch Prims.list) *
      (unit ->
         FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)))
  = fun projectee -> match projectee with | Match _0 -> _0
let (uu___is_UnreducedLet : atom -> Prims.bool) =
  fun projectee ->
    match projectee with | UnreducedLet _0 -> true | uu___ -> false
let (__proj__UnreducedLet__item___0 :
  atom ->
    (var * t FStarC_Thunk.t * t FStarC_Thunk.t * t FStarC_Thunk.t *
      FStarC_Syntax_Syntax.letbinding))
  = fun projectee -> match projectee with | UnreducedLet _0 -> _0
let (uu___is_UnreducedLetRec : atom -> Prims.bool) =
  fun projectee ->
    match projectee with | UnreducedLetRec _0 -> true | uu___ -> false
let (__proj__UnreducedLetRec__item___0 :
  atom ->
    ((var * t * t) Prims.list * t * FStarC_Syntax_Syntax.letbinding
      Prims.list))
  = fun projectee -> match projectee with | UnreducedLetRec _0 -> _0
let (uu___is_UVar : atom -> Prims.bool) =
  fun projectee -> match projectee with | UVar _0 -> true | uu___ -> false
let (__proj__UVar__item___0 :
  atom -> FStarC_Syntax_Syntax.term FStarC_Thunk.t) =
  fun projectee -> match projectee with | UVar _0 -> _0
let (uu___is_Lam_bs : lam_shape -> Prims.bool) =
  fun projectee -> match projectee with | Lam_bs _0 -> true | uu___ -> false
let (__proj__Lam_bs__item___0 :
  lam_shape ->
    (t Prims.list * FStarC_Syntax_Syntax.binders *
      FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option))
  = fun projectee -> match projectee with | Lam_bs _0 -> _0
let (uu___is_Lam_args : lam_shape -> Prims.bool) =
  fun projectee ->
    match projectee with | Lam_args _0 -> true | uu___ -> false
let (__proj__Lam_args__item___0 :
  lam_shape -> (t * FStarC_Syntax_Syntax.aqual) Prims.list) =
  fun projectee -> match projectee with | Lam_args _0 -> _0
let (uu___is_Lam_primop : lam_shape -> Prims.bool) =
  fun projectee ->
    match projectee with | Lam_primop _0 -> true | uu___ -> false
let (__proj__Lam_primop__item___0 :
  lam_shape ->
    (FStarC_Syntax_Syntax.fv * (t * FStarC_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | Lam_primop _0 -> _0
let (__proj__Mkt'__Lam__payload__item__interp :
  t'__Lam__payload -> (t * FStarC_Syntax_Syntax.aqual) Prims.list -> t) =
  fun projectee -> match projectee with | { interp; shape; arity;_} -> interp
let (__proj__Mkt'__Lam__payload__item__shape : t'__Lam__payload -> lam_shape)
  =
  fun projectee -> match projectee with | { interp; shape; arity;_} -> shape
let (__proj__Mkt'__Lam__payload__item__arity : t'__Lam__payload -> Prims.int)
  =
  fun projectee -> match projectee with | { interp; shape; arity;_} -> arity
let (uu___is_Lam : t' -> Prims.bool) =
  fun projectee -> match projectee with | Lam _0 -> true | uu___ -> false
let (__proj__Lam__item___0 : t' -> t'__Lam__payload) =
  fun projectee -> match projectee with | Lam _0 -> _0
let (uu___is_Accu : t' -> Prims.bool) =
  fun projectee -> match projectee with | Accu _0 -> true | uu___ -> false
let (__proj__Accu__item___0 :
  t' -> (atom * (t * FStarC_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee -> match projectee with | Accu _0 -> _0
let (uu___is_Construct : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Construct _0 -> true | uu___ -> false
let (__proj__Construct__item___0 :
  t' ->
    (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.universe Prims.list * (t
      * FStarC_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | Construct _0 -> _0
let (uu___is_FV : t' -> Prims.bool) =
  fun projectee -> match projectee with | FV _0 -> true | uu___ -> false
let (__proj__FV__item___0 :
  t' ->
    (FStarC_Syntax_Syntax.fv * FStarC_Syntax_Syntax.universe Prims.list * (t
      * FStarC_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | FV _0 -> _0
let (uu___is_Constant : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Constant _0 -> true | uu___ -> false
let (__proj__Constant__item___0 : t' -> constant) =
  fun projectee -> match projectee with | Constant _0 -> _0
let (uu___is_Type_t : t' -> Prims.bool) =
  fun projectee -> match projectee with | Type_t _0 -> true | uu___ -> false
let (__proj__Type_t__item___0 : t' -> FStarC_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Type_t _0 -> _0
let (uu___is_Univ : t' -> Prims.bool) =
  fun projectee -> match projectee with | Univ _0 -> true | uu___ -> false
let (__proj__Univ__item___0 : t' -> FStarC_Syntax_Syntax.universe) =
  fun projectee -> match projectee with | Univ _0 -> _0
let (uu___is_Unknown : t' -> Prims.bool) =
  fun projectee -> match projectee with | Unknown -> true | uu___ -> false
let (uu___is_Arrow : t' -> Prims.bool) =
  fun projectee -> match projectee with | Arrow _0 -> true | uu___ -> false
let (__proj__Arrow__item___0 :
  t' ->
    (FStarC_Syntax_Syntax.term FStarC_Thunk.t,
      ((t * FStarC_Syntax_Syntax.aqual) Prims.list * comp))
      FStar_Pervasives.either)
  = fun projectee -> match projectee with | Arrow _0 -> _0
let (uu___is_Refinement : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | Refinement _0 -> true | uu___ -> false
let (__proj__Refinement__item___0 :
  t' -> ((t -> t) * (unit -> (t * FStarC_Syntax_Syntax.aqual)))) =
  fun projectee -> match projectee with | Refinement _0 -> _0
let (uu___is_Reflect : t' -> Prims.bool) =
  fun projectee -> match projectee with | Reflect _0 -> true | uu___ -> false
let (__proj__Reflect__item___0 : t' -> t) =
  fun projectee -> match projectee with | Reflect _0 -> _0
let (uu___is_Quote : t' -> Prims.bool) =
  fun projectee -> match projectee with | Quote _0 -> true | uu___ -> false
let (__proj__Quote__item___0 :
  t' -> (FStarC_Syntax_Syntax.term * FStarC_Syntax_Syntax.quoteinfo)) =
  fun projectee -> match projectee with | Quote _0 -> _0
let (uu___is_Lazy : t' -> Prims.bool) =
  fun projectee -> match projectee with | Lazy _0 -> true | uu___ -> false
let (__proj__Lazy__item___0 :
  t' ->
    ((FStarC_Syntax_Syntax.lazyinfo,
      (FStarC_Dyn.dyn * FStarC_Syntax_Syntax.emb_typ))
      FStar_Pervasives.either * t FStarC_Thunk.t))
  = fun projectee -> match projectee with | Lazy _0 -> _0
let (uu___is_Meta : t' -> Prims.bool) =
  fun projectee -> match projectee with | Meta _0 -> true | uu___ -> false
let (__proj__Meta__item___0 :
  t' -> (t * FStarC_Syntax_Syntax.metadata FStarC_Thunk.t)) =
  fun projectee -> match projectee with | Meta _0 -> _0
let (uu___is_TopLevelLet : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelLet _0 -> true | uu___ -> false
let (__proj__TopLevelLet__item___0 :
  t' ->
    (FStarC_Syntax_Syntax.letbinding * Prims.int * (t *
      FStarC_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | TopLevelLet _0 -> _0
let (uu___is_TopLevelRec : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | TopLevelRec _0 -> true | uu___ -> false
let (__proj__TopLevelRec__item___0 :
  t' ->
    (FStarC_Syntax_Syntax.letbinding * Prims.int * Prims.bool Prims.list * (t
      * FStarC_Syntax_Syntax.aqual) Prims.list))
  = fun projectee -> match projectee with | TopLevelRec _0 -> _0
let (uu___is_LocalLetRec : t' -> Prims.bool) =
  fun projectee ->
    match projectee with | LocalLetRec _0 -> true | uu___ -> false
let (__proj__LocalLetRec__item___0 :
  t' ->
    (Prims.int * FStarC_Syntax_Syntax.letbinding *
      FStarC_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
      FStarC_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool
      Prims.list))
  = fun projectee -> match projectee with | LocalLetRec _0 -> _0
let (__proj__Mkt__item__nbe_t : t -> t') =
  fun projectee -> match projectee with | { nbe_t; nbe_r;_} -> nbe_t
let (__proj__Mkt__item__nbe_r : t -> FStarC_Compiler_Range_Type.range) =
  fun projectee -> match projectee with | { nbe_t; nbe_r;_} -> nbe_r
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee -> match projectee with | Tot _0 -> true | uu___ -> false
let (__proj__Tot__item___0 : comp -> t) =
  fun projectee -> match projectee with | Tot _0 -> _0
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee -> match projectee with | GTot _0 -> true | uu___ -> false
let (__proj__GTot__item___0 : comp -> t) =
  fun projectee -> match projectee with | GTot _0 -> _0
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee -> match projectee with | Comp _0 -> true | uu___ -> false
let (__proj__Comp__item___0 : comp -> comp_typ) =
  fun projectee -> match projectee with | Comp _0 -> _0
let (__proj__Mkcomp_typ__item__comp_univs :
  comp_typ -> FStarC_Syntax_Syntax.universes) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        comp_univs
let (__proj__Mkcomp_typ__item__effect_name : comp_typ -> FStarC_Ident.lident)
  =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        effect_name
let (__proj__Mkcomp_typ__item__result_typ : comp_typ -> t) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        result_typ
let (__proj__Mkcomp_typ__item__effect_args :
  comp_typ -> (t * FStarC_Syntax_Syntax.aqual) Prims.list) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        effect_args
let (__proj__Mkcomp_typ__item__flags : comp_typ -> cflag Prims.list) =
  fun projectee ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} -> flags
let (__proj__Mkresidual_comp__item__residual_effect :
  residual_comp -> FStarC_Ident.lident) =
  fun projectee ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_effect
let (__proj__Mkresidual_comp__item__residual_typ :
  residual_comp -> t FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_typ
let (__proj__Mkresidual_comp__item__residual_flags :
  residual_comp -> cflag Prims.list) =
  fun projectee ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_flags
let (uu___is_TOTAL : cflag -> Prims.bool) =
  fun projectee -> match projectee with | TOTAL -> true | uu___ -> false
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee -> match projectee with | MLEFFECT -> true | uu___ -> false
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee -> match projectee with | RETURN -> true | uu___ -> false
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | PARTIAL_RETURN -> true | uu___ -> false
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | SOMETRIVIAL -> true | uu___ -> false
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | TRIVIAL_POSTCONDITION -> true | uu___ -> false
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | SHOULD_NOT_INLINE -> true | uu___ -> false
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee -> match projectee with | LEMMA -> true | uu___ -> false
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee -> match projectee with | CPS -> true | uu___ -> false
let (uu___is_DECREASES_lex : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | DECREASES_lex _0 -> true | uu___ -> false
let (__proj__DECREASES_lex__item___0 : cflag -> t Prims.list) =
  fun projectee -> match projectee with | DECREASES_lex _0 -> _0
let (uu___is_DECREASES_wf : cflag -> Prims.bool) =
  fun projectee ->
    match projectee with | DECREASES_wf _0 -> true | uu___ -> false
let (__proj__DECREASES_wf__item___0 : cflag -> (t * t)) =
  fun projectee -> match projectee with | DECREASES_wf _0 -> _0
type arg = (t * FStarC_Syntax_Syntax.aqual)
type args = (t * FStarC_Syntax_Syntax.aqual) Prims.list
let (isAccu : t -> Prims.bool) =
  fun trm -> match trm.nbe_t with | Accu uu___ -> true | uu___ -> false
let (isNotAccu : t -> Prims.bool) =
  fun x -> match x.nbe_t with | Accu (uu___, uu___1) -> false | uu___ -> true
let (mk_rt : FStarC_Compiler_Range_Type.range -> t' -> t) =
  fun r -> fun t1 -> { nbe_t = t1; nbe_r = r }
let (mk_t : t' -> t) =
  fun t1 -> mk_rt FStarC_Compiler_Range_Type.dummyRange t1
let (nbe_t_of_t : t -> t') = fun t1 -> t1.nbe_t
let (mkConstruct :
  FStarC_Syntax_Syntax.fv ->
    FStarC_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i -> fun us -> fun ts -> mk_t (Construct (i, us, ts))
let (mkFV :
  FStarC_Syntax_Syntax.fv ->
    FStarC_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun i ->
    fun us ->
      fun ts ->
        let uu___ = FStarC_Syntax_Syntax.range_of_fv i in
        mk_rt uu___ (FV (i, us, ts))
let (mkAccuVar : var -> t) =
  fun v ->
    let uu___ = FStarC_Syntax_Syntax.range_of_bv v in
    mk_rt uu___ (Accu ((Var v), []))
let (mkAccuMatch :
  t ->
    (unit ->
       FStarC_Syntax_Syntax.match_returns_ascription
         FStar_Pervasives_Native.option)
      ->
      (unit -> FStarC_Syntax_Syntax.branch Prims.list) ->
        (unit ->
           FStarC_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option)
          -> t)
  =
  fun s ->
    fun ret -> fun bs -> fun rc -> mk_t (Accu ((Match (s, ret, bs, rc)), []))
let (equal_if : Prims.bool -> FStarC_TypeChecker_TermEqAndSimplify.eq_result)
  =
  fun uu___ ->
    if uu___
    then FStarC_TypeChecker_TermEqAndSimplify.Equal
    else FStarC_TypeChecker_TermEqAndSimplify.Unknown
let (equal_iff :
  Prims.bool -> FStarC_TypeChecker_TermEqAndSimplify.eq_result) =
  fun uu___ ->
    if uu___
    then FStarC_TypeChecker_TermEqAndSimplify.Equal
    else FStarC_TypeChecker_TermEqAndSimplify.NotEqual
let (eq_inj :
  FStarC_TypeChecker_TermEqAndSimplify.eq_result ->
    FStarC_TypeChecker_TermEqAndSimplify.eq_result ->
      FStarC_TypeChecker_TermEqAndSimplify.eq_result)
  =
  fun r1 ->
    fun r2 ->
      match (r1, r2) with
      | (FStarC_TypeChecker_TermEqAndSimplify.Equal,
         FStarC_TypeChecker_TermEqAndSimplify.Equal) ->
          FStarC_TypeChecker_TermEqAndSimplify.Equal
      | (FStarC_TypeChecker_TermEqAndSimplify.NotEqual, uu___) ->
          FStarC_TypeChecker_TermEqAndSimplify.NotEqual
      | (uu___, FStarC_TypeChecker_TermEqAndSimplify.NotEqual) ->
          FStarC_TypeChecker_TermEqAndSimplify.NotEqual
      | (FStarC_TypeChecker_TermEqAndSimplify.Unknown, uu___) ->
          FStarC_TypeChecker_TermEqAndSimplify.Unknown
      | (uu___, FStarC_TypeChecker_TermEqAndSimplify.Unknown) ->
          FStarC_TypeChecker_TermEqAndSimplify.Unknown
let (eq_and :
  FStarC_TypeChecker_TermEqAndSimplify.eq_result ->
    (unit -> FStarC_TypeChecker_TermEqAndSimplify.eq_result) ->
      FStarC_TypeChecker_TermEqAndSimplify.eq_result)
  =
  fun f ->
    fun g ->
      match f with
      | FStarC_TypeChecker_TermEqAndSimplify.Equal -> g ()
      | uu___ -> FStarC_TypeChecker_TermEqAndSimplify.Unknown
let (eq_constant :
  constant -> constant -> FStarC_TypeChecker_TermEqAndSimplify.eq_result) =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (Unit, Unit) -> FStarC_TypeChecker_TermEqAndSimplify.Equal
      | (Bool b1, Bool b2) -> equal_iff (b1 = b2)
      | (Int i1, Int i2) -> equal_iff (i1 = i2)
      | (String (s1, uu___), String (s2, uu___1)) -> equal_iff (s1 = s2)
      | (Char c11, Char c21) -> equal_iff (c11 = c21)
      | (Range r1, Range r2) -> FStarC_TypeChecker_TermEqAndSimplify.Unknown
      | (Real r1, Real r2) -> equal_if (r1 = r2)
      | (uu___, uu___1) -> FStarC_TypeChecker_TermEqAndSimplify.NotEqual
let rec (eq_t :
  FStarC_TypeChecker_Env.env_t ->
    t -> t -> FStarC_TypeChecker_TermEqAndSimplify.eq_result)
  =
  fun env ->
    fun t1 ->
      fun t2 ->
        match ((t1.nbe_t), (t2.nbe_t)) with
        | (Lam uu___, Lam uu___1) ->
            FStarC_TypeChecker_TermEqAndSimplify.Unknown
        | (Accu (a1, as1), Accu (a2, as2)) ->
            let uu___ = eq_atom a1 a2 in
            eq_and uu___ (fun uu___1 -> eq_args env as1 as2)
        | (Construct (v1, us1, args1), Construct (v2, us2, args2)) ->
            let uu___ = FStarC_Syntax_Syntax.fv_eq v1 v2 in
            if uu___
            then
              (if
                 (FStarC_Compiler_List.length args1) <>
                   (FStarC_Compiler_List.length args2)
               then failwith "eq_t, different number of args on Construct"
               else ();
               (let uu___2 =
                  let uu___3 = FStarC_Syntax_Syntax.lid_of_fv v1 in
                  FStarC_TypeChecker_Env.num_datacon_non_injective_ty_params
                    env uu___3 in
                match uu___2 with
                | FStar_Pervasives_Native.None ->
                    FStarC_TypeChecker_TermEqAndSimplify.Unknown
                | FStar_Pervasives_Native.Some n ->
                    if n <= (FStarC_Compiler_List.length args1)
                    then
                      let eq_args1 as1 as2 =
                        FStarC_Compiler_List.fold_left2
                          (fun acc ->
                             fun uu___3 ->
                               fun uu___4 ->
                                 match (uu___3, uu___4) with
                                 | ((a1, uu___5), (a2, uu___6)) ->
                                     let uu___7 = eq_t env a1 a2 in
                                     eq_inj acc uu___7)
                          FStarC_TypeChecker_TermEqAndSimplify.Equal as1 as2 in
                      let uu___3 = FStarC_Compiler_List.splitAt n args1 in
                      (match uu___3 with
                       | (parms1, args11) ->
                           let uu___4 = FStarC_Compiler_List.splitAt n args2 in
                           (match uu___4 with
                            | (parms2, args21) -> eq_args1 args11 args21))
                    else FStarC_TypeChecker_TermEqAndSimplify.Unknown))
            else FStarC_TypeChecker_TermEqAndSimplify.NotEqual
        | (FV (v1, us1, args1), FV (v2, us2, args2)) ->
            let uu___ = FStarC_Syntax_Syntax.fv_eq v1 v2 in
            if uu___
            then
              let uu___1 =
                let uu___2 = FStarC_Syntax_Util.eq_univs_list us1 us2 in
                equal_iff uu___2 in
              eq_and uu___1 (fun uu___2 -> eq_args env args1 args2)
            else FStarC_TypeChecker_TermEqAndSimplify.Unknown
        | (Constant c1, Constant c2) -> eq_constant c1 c2
        | (Type_t u1, Type_t u2) ->
            let uu___ = FStarC_Syntax_Util.eq_univs u1 u2 in equal_iff uu___
        | (Univ u1, Univ u2) ->
            let uu___ = FStarC_Syntax_Util.eq_univs u1 u2 in equal_iff uu___
        | (Refinement (r1, t11), Refinement (r2, t21)) ->
            let x =
              FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
                FStarC_Syntax_Syntax.t_unit in
            let uu___ =
              let uu___1 =
                let uu___2 = t11 () in FStar_Pervasives_Native.fst uu___2 in
              let uu___2 =
                let uu___3 = t21 () in FStar_Pervasives_Native.fst uu___3 in
              eq_t env uu___1 uu___2 in
            eq_and uu___
              (fun uu___1 ->
                 let uu___2 = let uu___3 = mkAccuVar x in r1 uu___3 in
                 let uu___3 = let uu___4 = mkAccuVar x in r2 uu___4 in
                 eq_t env uu___2 uu___3)
        | (Unknown, Unknown) -> FStarC_TypeChecker_TermEqAndSimplify.Equal
        | (uu___, uu___1) -> FStarC_TypeChecker_TermEqAndSimplify.Unknown
and (eq_atom :
  atom -> atom -> FStarC_TypeChecker_TermEqAndSimplify.eq_result) =
  fun a1 ->
    fun a2 ->
      match (a1, a2) with
      | (Var bv1, Var bv2) ->
          let uu___ = FStarC_Syntax_Syntax.bv_eq bv1 bv2 in equal_if uu___
      | (uu___, uu___1) -> FStarC_TypeChecker_TermEqAndSimplify.Unknown
and (eq_arg :
  FStarC_TypeChecker_Env.env_t ->
    arg -> arg -> FStarC_TypeChecker_TermEqAndSimplify.eq_result)
  =
  fun env ->
    fun a1 ->
      fun a2 ->
        eq_t env (FStar_Pervasives_Native.fst a1)
          (FStar_Pervasives_Native.fst a2)
and (eq_args :
  FStarC_TypeChecker_Env.env_t ->
    args -> args -> FStarC_TypeChecker_TermEqAndSimplify.eq_result)
  =
  fun env ->
    fun as1 ->
      fun as2 ->
        match (as1, as2) with
        | ([], []) -> FStarC_TypeChecker_TermEqAndSimplify.Equal
        | (x::xs, y::ys) ->
            let uu___ = eq_arg env x y in
            eq_and uu___ (fun uu___1 -> eq_args env xs ys)
        | (uu___, uu___1) -> FStarC_TypeChecker_TermEqAndSimplify.Unknown
let (constant_to_string : constant -> Prims.string) =
  fun c ->
    match c with
    | Unit -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStarC_BigInt.string_of_big_int i
    | Char c1 ->
        FStarC_Compiler_Util.format1 "'%s'"
          (FStarC_Compiler_Util.string_of_char c1)
    | String (s, uu___) -> FStarC_Compiler_Util.format1 "\"%s\"" s
    | Range r ->
        let uu___ = FStarC_Compiler_Range_Ops.string_of_range r in
        FStarC_Compiler_Util.format1 "Range %s" uu___
    | SConst s -> FStarC_Class_Show.show FStarC_Syntax_Print.showable_const s
    | Real s -> FStarC_Compiler_Util.format1 "Real %s" s
let rec (t_to_string : t -> Prims.string) =
  fun x ->
    match x.nbe_t with
    | Lam { interp = b; shape = uu___; arity;_} ->
        let uu___1 = FStarC_Compiler_Util.string_of_int arity in
        FStarC_Compiler_Util.format1 "Lam (_, %s args)" uu___1
    | Accu (a, l) ->
        let uu___ =
          let uu___1 = atom_to_string a in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStarC_Compiler_List.map
                    (fun x1 -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l in
                FStarC_Compiler_String.concat "; " uu___5 in
              Prims.strcat uu___4 ")" in
            Prims.strcat ") (" uu___3 in
          Prims.strcat uu___1 uu___2 in
        Prims.strcat "Accu (" uu___
    | Construct (fv, us, l) ->
        let uu___ =
          let uu___1 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_fv fv in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStarC_Compiler_List.map
                    (FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ)
                    us in
                FStarC_Compiler_String.concat "; " uu___5 in
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      FStarC_Compiler_List.map
                        (fun x1 ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l in
                    FStarC_Compiler_String.concat "; " uu___8 in
                  Prims.strcat uu___7 "]" in
                Prims.strcat "] [" uu___6 in
              Prims.strcat uu___4 uu___5 in
            Prims.strcat ") [" uu___3 in
          Prims.strcat uu___1 uu___2 in
        Prims.strcat "Construct (" uu___
    | FV (fv, us, l) ->
        let uu___ =
          let uu___1 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_fv fv in
          let uu___2 =
            let uu___3 =
              let uu___4 =
                let uu___5 =
                  FStarC_Compiler_List.map
                    (FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ)
                    us in
                FStarC_Compiler_String.concat "; " uu___5 in
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    let uu___8 =
                      FStarC_Compiler_List.map
                        (fun x1 ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l in
                    FStarC_Compiler_String.concat "; " uu___8 in
                  Prims.strcat uu___7 "]" in
                Prims.strcat "] [" uu___6 in
              Prims.strcat uu___4 uu___5 in
            Prims.strcat ") [" uu___3 in
          Prims.strcat uu___1 uu___2 in
        Prims.strcat "FV (" uu___
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu___ =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ u in
        Prims.strcat "Universe " uu___
    | Type_t u ->
        let uu___ =
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_univ u in
        Prims.strcat "Type_t " uu___
    | Arrow uu___ -> "Arrow"
    | Refinement (f, t1) ->
        let x1 =
          FStarC_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStarC_Syntax_Syntax.t_unit in
        let t2 = let uu___ = t1 () in FStar_Pervasives_Native.fst uu___ in
        let uu___ =
          let uu___1 =
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv x1 in
          let uu___2 =
            let uu___3 =
              let uu___4 = t_to_string t2 in
              let uu___5 =
                let uu___6 =
                  let uu___7 =
                    let uu___8 = let uu___9 = mkAccuVar x1 in f uu___9 in
                    t_to_string uu___8 in
                  Prims.strcat uu___7 "}" in
                Prims.strcat "{" uu___6 in
              Prims.strcat uu___4 uu___5 in
            Prims.strcat ":" uu___3 in
          Prims.strcat uu___1 uu___2 in
        Prims.strcat "Refinement " uu___
    | Unknown -> "Unknown"
    | Reflect t1 ->
        let uu___ = t_to_string t1 in Prims.strcat "Reflect " uu___
    | Quote uu___ -> "Quote _"
    | Lazy (FStar_Pervasives.Inl li, uu___) ->
        let uu___1 =
          let uu___2 = FStarC_Syntax_Util.unfold_lazy li in
          FStarC_Class_Show.show FStarC_Syntax_Print.showable_term uu___2 in
        FStarC_Compiler_Util.format1 "Lazy (Inl {%s})" uu___1
    | Lazy (FStar_Pervasives.Inr (uu___, et), uu___1) ->
        let uu___2 =
          FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_emb_typ et in
        FStarC_Compiler_Util.format1 "Lazy (Inr (?, %s))" uu___2
    | LocalLetRec (uu___, l, uu___1, uu___2, uu___3, uu___4, uu___5) ->
        let uu___6 =
          let uu___7 =
            FStarC_Class_Show.show
              (FStarC_Class_Show.show_tuple2 FStarC_Class_Show.showable_bool
                 (FStarC_Class_Show.show_list
                    FStarC_Syntax_Print.showable_letbinding)) (true, [l]) in
          Prims.strcat uu___7 ")" in
        Prims.strcat "LocalLetRec (" uu___6
    | TopLevelLet (lb, uu___, uu___1) ->
        let uu___2 =
          let uu___3 =
            let uu___4 =
              FStarC_Compiler_Util.right lb.FStarC_Syntax_Syntax.lbname in
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_fv uu___4 in
          Prims.strcat uu___3 ")" in
        Prims.strcat "TopLevelLet (" uu___2
    | TopLevelRec (lb, uu___, uu___1, uu___2) ->
        let uu___3 =
          let uu___4 =
            let uu___5 =
              FStarC_Compiler_Util.right lb.FStarC_Syntax_Syntax.lbname in
            FStarC_Class_Show.show FStarC_Syntax_Print.showable_fv uu___5 in
          Prims.strcat uu___4 ")" in
        Prims.strcat "TopLevelRec (" uu___3
    | Meta (t1, uu___) ->
        let uu___1 = t_to_string t1 in Prims.strcat "Meta " uu___1
and (atom_to_string : atom -> Prims.string) =
  fun a ->
    match a with
    | Var v ->
        let uu___ = FStarC_Class_Show.show FStarC_Syntax_Print.showable_bv v in
        Prims.strcat "Var " uu___
    | Match (t1, uu___, uu___1, uu___2) ->
        let uu___3 = t_to_string t1 in Prims.strcat "Match " uu___3
    | UnreducedLet (var1, typ, def, body, lb) ->
        let uu___ =
          let uu___1 =
            FStarC_Class_Show.show
              (FStarC_Class_Show.show_tuple2 FStarC_Class_Show.showable_bool
                 (FStarC_Class_Show.show_list
                    FStarC_Syntax_Print.showable_letbinding)) (false, [lb]) in
          Prims.strcat uu___1 " in ...)" in
        Prims.strcat "UnreducedLet(" uu___
    | UnreducedLetRec (uu___, body, lbs) ->
        let uu___1 =
          let uu___2 =
            FStarC_Class_Show.show
              (FStarC_Class_Show.show_tuple2 FStarC_Class_Show.showable_bool
                 (FStarC_Class_Show.show_list
                    FStarC_Syntax_Print.showable_letbinding)) (true, lbs) in
          let uu___3 =
            let uu___4 =
              let uu___5 = t_to_string body in Prims.strcat uu___5 ")" in
            Prims.strcat " in " uu___4 in
          Prims.strcat uu___2 uu___3 in
        Prims.strcat "UnreducedLetRec(" uu___1
    | UVar uu___ -> "UVar"
let (arg_to_string : arg -> Prims.string) =
  fun a -> t_to_string (FStar_Pervasives_Native.fst a)
let (args_to_string : args -> Prims.string) =
  fun args1 ->
    let uu___ = FStarC_Compiler_List.map arg_to_string args1 in
    FStarC_Compiler_String.concat " " uu___
let (showable_t : t FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = t_to_string }
let (showable_args : args FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = args_to_string }
type head = t
type annot = t FStar_Pervasives_Native.option
type nbe_cbs =
  {
  iapp: t -> args -> t ;
  translate: FStarC_Syntax_Syntax.term -> t }
let (__proj__Mknbe_cbs__item__iapp : nbe_cbs -> t -> args -> t) =
  fun projectee -> match projectee with | { iapp; translate;_} -> iapp
let (__proj__Mknbe_cbs__item__translate :
  nbe_cbs -> FStarC_Syntax_Syntax.term -> t) =
  fun projectee -> match projectee with | { iapp; translate;_} -> translate
type 'a embedding =
  {
  em: nbe_cbs -> 'a -> t ;
  un: nbe_cbs -> t -> 'a FStar_Pervasives_Native.option ;
  typ: unit -> t ;
  e_typ: unit -> FStarC_Syntax_Syntax.emb_typ }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> nbe_cbs -> 'a -> t =
  fun projectee -> match projectee with | { em; un; typ; e_typ;_} -> em
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> nbe_cbs -> t -> 'a FStar_Pervasives_Native.option =
  fun projectee -> match projectee with | { em; un; typ; e_typ;_} -> un
let __proj__Mkembedding__item__typ : 'a . 'a embedding -> unit -> t =
  fun projectee -> match projectee with | { em; un; typ; e_typ;_} -> typ
let __proj__Mkembedding__item__e_typ :
  'a . 'a embedding -> unit -> FStarC_Syntax_Syntax.emb_typ =
  fun projectee -> match projectee with | { em; un; typ; e_typ;_} -> e_typ
let em : 'a . 'a embedding -> nbe_cbs -> 'a -> t =
  fun projectee ->
    match projectee with | { em = em1; un; typ; e_typ;_} -> em1
let un :
  'a . 'a embedding -> nbe_cbs -> t -> 'a FStar_Pervasives_Native.option =
  fun projectee ->
    match projectee with | { em = em1; un = un1; typ; e_typ;_} -> un1
let typ : 'a . 'a embedding -> unit -> t =
  fun projectee ->
    match projectee with | { em = em1; un = un1; typ = typ1; e_typ;_} -> typ1
let e_typ : 'a . 'a embedding -> unit -> FStarC_Syntax_Syntax.emb_typ =
  fun projectee ->
    match projectee with
    | { em = em1; un = un1; typ = typ1; e_typ = e_typ1;_} -> e_typ1
let (iapp_cb : nbe_cbs -> t -> args -> t) =
  fun cbs -> fun h -> fun a -> cbs.iapp h a
let (translate_cb : nbe_cbs -> FStarC_Syntax_Syntax.term -> t) =
  fun cbs -> fun t1 -> cbs.translate t1
let embed : 'a . 'a embedding -> nbe_cbs -> 'a -> t =
  fun e -> fun cb -> fun x -> e.em cb x
let unembed :
  'a . 'a embedding -> nbe_cbs -> t -> 'a FStar_Pervasives_Native.option =
  fun e -> fun cb -> fun trm -> e.un cb trm
let type_of : 'a . 'a embedding -> t = fun e -> e.typ ()
let set_type : 'a . t -> 'a embedding -> 'a embedding =
  fun ty ->
    fun e ->
      { em = (e.em); un = (e.un); typ = (fun uu___ -> ty); e_typ = (e.e_typ)
      }
let mk_emb :
  'a .
    (nbe_cbs -> 'a -> t) ->
      (nbe_cbs -> t -> 'a FStar_Pervasives_Native.option) ->
        (unit -> t) -> (unit -> FStarC_Syntax_Syntax.emb_typ) -> 'a embedding
  =
  fun em1 ->
    fun un1 ->
      fun typ1 -> fun et -> { em = em1; un = un1; typ = typ1; e_typ = et }
let mk_emb' :
  'uuuuu .
    (nbe_cbs -> 'uuuuu -> t') ->
      (nbe_cbs -> t' -> 'uuuuu FStar_Pervasives_Native.option) ->
        (unit -> t) ->
          (unit -> FStarC_Syntax_Syntax.emb_typ) -> 'uuuuu embedding
  =
  fun em1 ->
    fun un1 ->
      mk_emb (fun cbs -> fun t1 -> let uu___ = em1 cbs t1 in mk_t uu___)
        (fun cbs -> fun t1 -> un1 cbs t1.nbe_t)
let embed_as :
  'a 'b .
    'a embedding ->
      ('a -> 'b) ->
        ('b -> 'a) -> t FStar_Pervasives_Native.option -> 'b embedding
  =
  fun ea ->
    fun ab ->
      fun ba ->
        fun ot ->
          mk_emb (fun cbs -> fun x -> let uu___ = ba x in embed ea cbs uu___)
            (fun cbs ->
               fun t1 ->
                 let uu___ = unembed ea cbs t1 in
                 FStarC_Compiler_Util.map_opt uu___ ab)
            (fun uu___ ->
               match ot with
               | FStar_Pervasives_Native.Some t1 -> t1
               | FStar_Pervasives_Native.None -> ea.typ ()) ea.e_typ
let (lid_as_constr :
  FStarC_Ident.lident ->
    FStarC_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l ->
    fun us ->
      fun args1 ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv l
            (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor) in
        mkConstruct uu___ us args1
let (lid_as_typ :
  FStarC_Ident.lident ->
    FStarC_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l ->
    fun us ->
      fun args1 ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv l FStar_Pervasives_Native.None in
        mkFV uu___ us args1
let (as_iarg : t -> arg) =
  fun a ->
    let uu___ = FStarC_Syntax_Syntax.as_aqual_implicit true in (a, uu___)
let (as_arg : t -> arg) = fun a -> (a, FStar_Pervasives_Native.None)
let (make_arrow1 : t -> arg -> t) =
  fun t1 -> fun a -> mk_t (Arrow (FStar_Pervasives.Inr ([a], (Tot t1))))
let lazy_embed :
  'a . (unit -> FStarC_Syntax_Syntax.emb_typ) -> 'a -> (unit -> t) -> t =
  fun et ->
    fun x ->
      fun f ->
        (let uu___1 =
           FStarC_Compiler_Effect.op_Bang FStarC_Options.debug_embedding in
         if uu___1
         then
           let uu___2 =
             let uu___3 = et () in
             FStarC_Class_Show.show FStarC_Syntax_Syntax.showable_emb_typ
               uu___3 in
           FStarC_Compiler_Util.print1 "Embedding\n\temb_typ=%s\n" uu___2
         else ());
        (let uu___1 =
           FStarC_Compiler_Effect.op_Bang FStarC_Options.eager_embedding in
         if uu___1
         then f ()
         else
           (let thunk = FStarC_Thunk.mk f in
            let li =
              let uu___3 = FStarC_Dyn.mkdyn x in
              let uu___4 = et () in (uu___3, uu___4) in
            mk_t (Lazy ((FStar_Pervasives.Inr li), thunk))))
let lazy_unembed :
  'a .
    (unit -> FStarC_Syntax_Syntax.emb_typ) ->
      t ->
        (t -> 'a FStar_Pervasives_Native.option) ->
          'a FStar_Pervasives_Native.option
  =
  fun et ->
    fun x ->
      fun f ->
        match x.nbe_t with
        | Lazy (FStar_Pervasives.Inl li, thunk) ->
            let uu___ = FStarC_Thunk.force thunk in f uu___
        | Lazy (FStar_Pervasives.Inr (b, et'), thunk) ->
            let uu___ =
              (let uu___1 = et () in uu___1 <> et') ||
                (FStarC_Compiler_Effect.op_Bang
                   FStarC_Options.eager_embedding) in
            if uu___
            then
              let res = let uu___1 = FStarC_Thunk.force thunk in f uu___1 in
              ((let uu___2 =
                  FStarC_Compiler_Effect.op_Bang
                    FStarC_Options.debug_embedding in
                if uu___2
                then
                  let uu___3 =
                    let uu___4 = et () in
                    FStarC_Class_Show.show
                      FStarC_Syntax_Syntax.showable_emb_typ uu___4 in
                  let uu___4 =
                    FStarC_Class_Show.show
                      FStarC_Syntax_Syntax.showable_emb_typ et' in
                  FStarC_Compiler_Util.print2
                    "Unembed cancellation failed\n\t%s <> %s\n" uu___3 uu___4
                else ());
               res)
            else
              (let a1 = FStarC_Dyn.undyn b in
               (let uu___3 =
                  FStarC_Compiler_Effect.op_Bang
                    FStarC_Options.debug_embedding in
                if uu___3
                then
                  let uu___4 =
                    let uu___5 = et () in
                    FStarC_Class_Show.show
                      FStarC_Syntax_Syntax.showable_emb_typ uu___5 in
                  FStarC_Compiler_Util.print1 "Unembed cancelled for %s\n"
                    uu___4
                else ());
               FStar_Pervasives_Native.Some a1)
        | uu___ ->
            let aopt = f x in
            ((let uu___2 =
                FStarC_Compiler_Effect.op_Bang FStarC_Options.debug_embedding in
              if uu___2
              then
                let uu___3 =
                  let uu___4 = et () in
                  FStarC_Class_Show.show
                    FStarC_Syntax_Syntax.showable_emb_typ uu___4 in
                FStarC_Compiler_Util.print1 "Unembedding:\n\temb_typ=%s\n"
                  uu___3
              else ());
             aopt)
let lazy_unembed_lazy_kind :
  'a .
    FStarC_Syntax_Syntax.lazy_kind -> t -> 'a FStar_Pervasives_Native.option
  =
  fun k ->
    fun x ->
      match x.nbe_t with
      | Lazy (FStar_Pervasives.Inl li, uu___) ->
          if li.FStarC_Syntax_Syntax.lkind = k
          then
            let uu___1 = FStarC_Dyn.undyn li.FStarC_Syntax_Syntax.blob in
            FStar_Pervasives_Native.Some uu___1
          else FStar_Pervasives_Native.None
      | uu___ -> FStar_Pervasives_Native.None
type abstract_nbe_term =
  | AbstractNBE of t 
let (uu___is_AbstractNBE : abstract_nbe_term -> Prims.bool) =
  fun projectee -> true
let (__proj__AbstractNBE__item__t : abstract_nbe_term -> t) =
  fun projectee -> match projectee with | AbstractNBE t1 -> t1
let (mk_any_emb : t -> t embedding) =
  fun ty ->
    let em1 _cb a = a in
    let un1 _cb t1 = FStar_Pervasives_Native.Some t1 in
    mk_emb em1 un1 (fun uu___ -> ty)
      (fun uu___ -> FStarC_Syntax_Syntax.ET_abstract)
let (e_any : t embedding) =
  let em1 _cb a = a in
  let un1 _cb t1 = FStar_Pervasives_Native.Some t1 in
  mk_emb em1 un1 (fun uu___ -> lid_as_typ FStarC_Parser_Const.term_lid [] [])
    (fun uu___ -> FStarC_Syntax_Syntax.ET_abstract)
let (e_unit : unit embedding) =
  let em1 _cb a = Constant Unit in
  let un1 _cb t1 = FStar_Pervasives_Native.Some () in
  mk_emb' em1 un1
    (fun uu___ -> lid_as_typ FStarC_Parser_Const.unit_lid [] [])
    (FStarC_Syntax_Embeddings_Base.emb_typ_of FStarC_Syntax_Embeddings.e_unit)
let (e_bool : Prims.bool embedding) =
  let em1 _cb a = Constant (Bool a) in
  let un1 _cb t1 =
    match t1 with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu___ -> FStar_Pervasives_Native.None in
  mk_emb' em1 un1
    (fun uu___ -> lid_as_typ FStarC_Parser_Const.bool_lid [] [])
    (FStarC_Syntax_Embeddings_Base.emb_typ_of FStarC_Syntax_Embeddings.e_bool)
let (e_char : FStar_String.char embedding) =
  let em1 _cb c = Constant (Char c) in
  let un1 _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu___ -> FStar_Pervasives_Native.None in
  mk_emb' em1 un1
    (fun uu___ -> lid_as_typ FStarC_Parser_Const.char_lid [] [])
    (FStarC_Syntax_Embeddings_Base.emb_typ_of FStarC_Syntax_Embeddings.e_char)
let (e_string : Prims.string embedding) =
  let em1 _cb s =
    Constant (String (s, FStarC_Compiler_Range_Type.dummyRange)) in
  let un1 _cb s =
    match s with
    | Constant (String (s1, uu___)) -> FStar_Pervasives_Native.Some s1
    | uu___ -> FStar_Pervasives_Native.None in
  mk_emb' em1 un1
    (fun uu___ -> lid_as_typ FStarC_Parser_Const.string_lid [] [])
    (FStarC_Syntax_Embeddings_Base.emb_typ_of
       FStarC_Syntax_Embeddings.e_string)
let (e_int : FStarC_BigInt.t embedding) =
  let em1 _cb c = Constant (Int c) in
  let un1 _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu___ -> FStar_Pervasives_Native.None in
  mk_emb' em1 un1 (fun uu___ -> lid_as_typ FStarC_Parser_Const.int_lid [] [])
    (FStarC_Syntax_Embeddings_Base.emb_typ_of
       FStarC_Syntax_Embeddings.e_fsint)
let (e_real : FStarC_Compiler_Real.real embedding) =
  let em1 _cb uu___ =
    match uu___ with | FStarC_Compiler_Real.Real c -> Constant (Real c) in
  let un1 _cb c =
    match c with
    | Constant (Real a) ->
        FStar_Pervasives_Native.Some (FStarC_Compiler_Real.Real a)
    | uu___ -> FStar_Pervasives_Native.None in
  mk_emb' em1 un1
    (fun uu___ -> lid_as_typ FStarC_Parser_Const.real_lid [] [])
    (FStarC_Syntax_Embeddings_Base.emb_typ_of FStarC_Syntax_Embeddings.e_real)
let (e_fsint : Prims.int embedding) =
  embed_as e_int FStarC_BigInt.to_int_fs FStarC_BigInt.of_int_fs
    FStar_Pervasives_Native.None
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea ->
    let etyp uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_Ident.string_of_lid FStarC_Parser_Const.option_lid in
        let uu___3 = let uu___4 = ea.e_typ () in [uu___4] in (uu___2, uu___3) in
      FStarC_Syntax_Syntax.ET_app uu___1 in
    let em1 cb o =
      lazy_embed etyp o
        (fun uu___ ->
           match o with
           | FStar_Pervasives_Native.None ->
               let uu___1 =
                 let uu___2 = let uu___3 = type_of ea in as_iarg uu___3 in
                 [uu___2] in
               lid_as_constr FStarC_Parser_Const.none_lid
                 [FStarC_Syntax_Syntax.U_zero] uu___1
           | FStar_Pervasives_Native.Some x ->
               let uu___1 =
                 let uu___2 = let uu___3 = embed ea cb x in as_arg uu___3 in
                 let uu___3 =
                   let uu___4 = let uu___5 = type_of ea in as_iarg uu___5 in
                   [uu___4] in
                 uu___2 :: uu___3 in
               lid_as_constr FStarC_Parser_Const.some_lid
                 [FStarC_Syntax_Syntax.U_zero] uu___1) in
    let un1 cb trm =
      lazy_unembed etyp trm
        (fun trm1 ->
           match trm1.nbe_t with
           | Construct (fvar, us, args1) when
               FStarC_Syntax_Syntax.fv_eq_lid fvar
                 FStarC_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar, us, (a1, uu___)::uu___1::[]) when
               FStarC_Syntax_Syntax.fv_eq_lid fvar
                 FStarC_Parser_Const.some_lid
               ->
               let uu___2 = unembed ea cb a1 in
               FStarC_Compiler_Util.bind_opt uu___2
                 (fun a2 ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a2))
           | uu___ -> FStar_Pervasives_Native.None) in
    mk_emb em1 un1
      (fun uu___ ->
         let uu___1 =
           let uu___2 = let uu___3 = type_of ea in as_arg uu___3 in [uu___2] in
         lid_as_typ FStarC_Parser_Const.option_lid
           [FStarC_Syntax_Syntax.U_zero] uu___1) etyp
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea ->
    fun eb ->
      let etyp uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Ident.string_of_lid FStarC_Parser_Const.lid_tuple2 in
          let uu___3 =
            let uu___4 = ea.e_typ () in
            let uu___5 = let uu___6 = eb.e_typ () in [uu___6] in uu___4 ::
              uu___5 in
          (uu___2, uu___3) in
        FStarC_Syntax_Syntax.ET_app uu___1 in
      let em1 cb x =
        lazy_embed etyp x
          (fun uu___ ->
             let uu___1 =
               let uu___2 =
                 let uu___3 = embed eb cb (FStar_Pervasives_Native.snd x) in
                 as_arg uu___3 in
               let uu___3 =
                 let uu___4 =
                   let uu___5 = embed ea cb (FStar_Pervasives_Native.fst x) in
                   as_arg uu___5 in
                 let uu___5 =
                   let uu___6 = let uu___7 = type_of eb in as_iarg uu___7 in
                   let uu___7 =
                     let uu___8 = let uu___9 = type_of ea in as_iarg uu___9 in
                     [uu___8] in
                   uu___6 :: uu___7 in
                 uu___4 :: uu___5 in
               uu___2 :: uu___3 in
             lid_as_constr FStarC_Parser_Const.lid_Mktuple2
               [FStarC_Syntax_Syntax.U_zero; FStarC_Syntax_Syntax.U_zero]
               uu___1) in
      let un1 cb trm =
        lazy_unembed etyp trm
          (fun uu___ ->
             (fun trm1 ->
                match trm1.nbe_t with
                | Construct
                    (fvar, us, (b1, uu___)::(a1, uu___1)::uu___2::uu___3::[])
                    when
                    FStarC_Syntax_Syntax.fv_eq_lid fvar
                      FStarC_Parser_Const.lid_Mktuple2
                    ->
                    Obj.magic
                      (Obj.repr
                         (let uu___4 = unembed ea cb a1 in
                          FStarC_Class_Monad.op_let_Bang
                            FStarC_Class_Monad.monad_option () ()
                            (Obj.magic uu___4)
                            (fun uu___5 ->
                               (fun a2 ->
                                  let a2 = Obj.magic a2 in
                                  let uu___5 = unembed eb cb b1 in
                                  Obj.magic
                                    (FStarC_Class_Monad.op_let_Bang
                                       FStarC_Class_Monad.monad_option () ()
                                       (Obj.magic uu___5)
                                       (fun uu___6 ->
                                          (fun b2 ->
                                             let b2 = Obj.magic b2 in
                                             Obj.magic
                                               (FStar_Pervasives_Native.Some
                                                  (a2, b2))) uu___6))) uu___5)))
                | uu___ -> Obj.magic (Obj.repr FStar_Pervasives_Native.None))
               uu___) in
      mk_emb em1 un1
        (fun uu___ ->
           let uu___1 =
             let uu___2 = let uu___3 = type_of eb in as_arg uu___3 in
             let uu___3 =
               let uu___4 = let uu___5 = type_of ea in as_arg uu___5 in
               [uu___4] in
             uu___2 :: uu___3 in
           lid_as_typ FStarC_Parser_Const.lid_tuple2
             [FStarC_Syntax_Syntax.U_zero; FStarC_Syntax_Syntax.U_zero]
             uu___1) etyp
let e_tuple3 :
  'a 'b 'c .
    'a embedding -> 'b embedding -> 'c embedding -> ('a * 'b * 'c) embedding
  =
  fun ea ->
    fun eb ->
      fun ec ->
        let etyp uu___ =
          let uu___1 =
            let uu___2 =
              FStarC_Ident.string_of_lid FStarC_Parser_Const.lid_tuple3 in
            let uu___3 =
              let uu___4 = ea.e_typ () in
              let uu___5 =
                let uu___6 = eb.e_typ () in
                let uu___7 = let uu___8 = ec.e_typ () in [uu___8] in uu___6
                  :: uu___7 in
              uu___4 :: uu___5 in
            (uu___2, uu___3) in
          FStarC_Syntax_Syntax.ET_app uu___1 in
        let em1 cb uu___ =
          match uu___ with
          | (x1, x2, x3) ->
              lazy_embed etyp (x1, x2, x3)
                (fun uu___1 ->
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = embed ec cb x3 in as_arg uu___4 in
                     let uu___4 =
                       let uu___5 =
                         let uu___6 = embed eb cb x2 in as_arg uu___6 in
                       let uu___6 =
                         let uu___7 =
                           let uu___8 = embed ea cb x1 in as_arg uu___8 in
                         let uu___8 =
                           let uu___9 =
                             let uu___10 = type_of ec in as_iarg uu___10 in
                           let uu___10 =
                             let uu___11 =
                               let uu___12 = type_of eb in as_iarg uu___12 in
                             let uu___12 =
                               let uu___13 =
                                 let uu___14 = type_of ea in as_iarg uu___14 in
                               [uu___13] in
                             uu___11 :: uu___12 in
                           uu___9 :: uu___10 in
                         uu___7 :: uu___8 in
                       uu___5 :: uu___6 in
                     uu___3 :: uu___4 in
                   lid_as_constr FStarC_Parser_Const.lid_Mktuple3
                     [FStarC_Syntax_Syntax.U_zero;
                     FStarC_Syntax_Syntax.U_zero;
                     FStarC_Syntax_Syntax.U_zero] uu___2) in
        let un1 cb trm =
          lazy_unembed etyp trm
            (fun uu___ ->
               (fun trm1 ->
                  match trm1.nbe_t with
                  | Construct
                      (fvar, us,
                       (c1, uu___)::(b1, uu___1)::(a1, uu___2)::uu___3::uu___4::uu___5::[])
                      when
                      FStarC_Syntax_Syntax.fv_eq_lid fvar
                        FStarC_Parser_Const.lid_Mktuple3
                      ->
                      Obj.magic
                        (Obj.repr
                           (let uu___6 = unembed ea cb a1 in
                            FStarC_Class_Monad.op_let_Bang
                              FStarC_Class_Monad.monad_option () ()
                              (Obj.magic uu___6)
                              (fun uu___7 ->
                                 (fun a2 ->
                                    let a2 = Obj.magic a2 in
                                    let uu___7 = unembed eb cb b1 in
                                    Obj.magic
                                      (FStarC_Class_Monad.op_let_Bang
                                         FStarC_Class_Monad.monad_option ()
                                         () (Obj.magic uu___7)
                                         (fun uu___8 ->
                                            (fun b2 ->
                                               let b2 = Obj.magic b2 in
                                               let uu___8 = unembed ec cb c1 in
                                               Obj.magic
                                                 (FStarC_Class_Monad.op_let_Bang
                                                    FStarC_Class_Monad.monad_option
                                                    () () (Obj.magic uu___8)
                                                    (fun uu___9 ->
                                                       (fun c2 ->
                                                          let c2 =
                                                            Obj.magic c2 in
                                                          Obj.magic
                                                            (FStar_Pervasives_Native.Some
                                                               (a2, b2, c2)))
                                                         uu___9))) uu___8)))
                                   uu___7)))
                  | uu___ ->
                      Obj.magic (Obj.repr FStar_Pervasives_Native.None))
                 uu___) in
        mk_emb em1 un1
          (fun uu___ ->
             let uu___1 =
               let uu___2 = let uu___3 = type_of ec in as_arg uu___3 in
               let uu___3 =
                 let uu___4 = let uu___5 = type_of eb in as_arg uu___5 in
                 let uu___5 =
                   let uu___6 = let uu___7 = type_of ea in as_arg uu___7 in
                   [uu___6] in
                 uu___4 :: uu___5 in
               uu___2 :: uu___3 in
             lid_as_typ FStarC_Parser_Const.lid_tuple3
               [FStarC_Syntax_Syntax.U_zero;
               FStarC_Syntax_Syntax.U_zero;
               FStarC_Syntax_Syntax.U_zero] uu___1) etyp
let e_tuple4 :
  'a 'b 'c 'd .
    'a embedding ->
      'b embedding ->
        'c embedding -> 'd embedding -> ('a * 'b * 'c * 'd) embedding
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          let etyp uu___ =
            let uu___1 =
              let uu___2 =
                FStarC_Ident.string_of_lid FStarC_Parser_Const.lid_tuple4 in
              let uu___3 =
                let uu___4 = ea.e_typ () in
                let uu___5 =
                  let uu___6 = eb.e_typ () in
                  let uu___7 =
                    let uu___8 = ec.e_typ () in
                    let uu___9 = let uu___10 = ed.e_typ () in [uu___10] in
                    uu___8 :: uu___9 in
                  uu___6 :: uu___7 in
                uu___4 :: uu___5 in
              (uu___2, uu___3) in
            FStarC_Syntax_Syntax.ET_app uu___1 in
          let em1 cb uu___ =
            match uu___ with
            | (x1, x2, x3, x4) ->
                lazy_embed etyp (x1, x2, x3, x4)
                  (fun uu___1 ->
                     let uu___2 =
                       let uu___3 =
                         let uu___4 = embed ed cb x4 in as_arg uu___4 in
                       let uu___4 =
                         let uu___5 =
                           let uu___6 = embed ec cb x3 in as_arg uu___6 in
                         let uu___6 =
                           let uu___7 =
                             let uu___8 = embed eb cb x2 in as_arg uu___8 in
                           let uu___8 =
                             let uu___9 =
                               let uu___10 = embed ea cb x1 in as_arg uu___10 in
                             let uu___10 =
                               let uu___11 =
                                 let uu___12 = type_of ed in as_iarg uu___12 in
                               let uu___12 =
                                 let uu___13 =
                                   let uu___14 = type_of ec in
                                   as_iarg uu___14 in
                                 let uu___14 =
                                   let uu___15 =
                                     let uu___16 = type_of eb in
                                     as_iarg uu___16 in
                                   let uu___16 =
                                     let uu___17 =
                                       let uu___18 = type_of ea in
                                       as_iarg uu___18 in
                                     [uu___17] in
                                   uu___15 :: uu___16 in
                                 uu___13 :: uu___14 in
                               uu___11 :: uu___12 in
                             uu___9 :: uu___10 in
                           uu___7 :: uu___8 in
                         uu___5 :: uu___6 in
                       uu___3 :: uu___4 in
                     lid_as_constr FStarC_Parser_Const.lid_Mktuple4
                       [FStarC_Syntax_Syntax.U_zero;
                       FStarC_Syntax_Syntax.U_zero;
                       FStarC_Syntax_Syntax.U_zero;
                       FStarC_Syntax_Syntax.U_zero] uu___2) in
          let un1 cb trm =
            lazy_unembed etyp trm
              (fun uu___ ->
                 (fun trm1 ->
                    match trm1.nbe_t with
                    | Construct
                        (fvar, us,
                         (d1, uu___)::(c1, uu___1)::(b1, uu___2)::(a1,
                                                                   uu___3)::uu___4::uu___5::uu___6::uu___7::[])
                        when
                        FStarC_Syntax_Syntax.fv_eq_lid fvar
                          FStarC_Parser_Const.lid_Mktuple4
                        ->
                        Obj.magic
                          (Obj.repr
                             (let uu___8 = unembed ea cb a1 in
                              FStarC_Class_Monad.op_let_Bang
                                FStarC_Class_Monad.monad_option () ()
                                (Obj.magic uu___8)
                                (fun uu___9 ->
                                   (fun a2 ->
                                      let a2 = Obj.magic a2 in
                                      let uu___9 = unembed eb cb b1 in
                                      Obj.magic
                                        (FStarC_Class_Monad.op_let_Bang
                                           FStarC_Class_Monad.monad_option ()
                                           () (Obj.magic uu___9)
                                           (fun uu___10 ->
                                              (fun b2 ->
                                                 let b2 = Obj.magic b2 in
                                                 let uu___10 =
                                                   unembed ec cb c1 in
                                                 Obj.magic
                                                   (FStarC_Class_Monad.op_let_Bang
                                                      FStarC_Class_Monad.monad_option
                                                      () ()
                                                      (Obj.magic uu___10)
                                                      (fun uu___11 ->
                                                         (fun c2 ->
                                                            let c2 =
                                                              Obj.magic c2 in
                                                            let uu___11 =
                                                              unembed ed cb
                                                                d1 in
                                                            Obj.magic
                                                              (FStarC_Class_Monad.op_let_Bang
                                                                 FStarC_Class_Monad.monad_option
                                                                 () ()
                                                                 (Obj.magic
                                                                    uu___11)
                                                                 (fun uu___12
                                                                    ->
                                                                    (fun d2
                                                                    ->
                                                                    let d2 =
                                                                    Obj.magic
                                                                    d2 in
                                                                    Obj.magic
                                                                    (FStar_Pervasives_Native.Some
                                                                    (a2, b2,
                                                                    c2, d2)))
                                                                    uu___12)))
                                                           uu___11))) uu___10)))
                                     uu___9)))
                    | uu___ ->
                        Obj.magic (Obj.repr FStar_Pervasives_Native.None))
                   uu___) in
          mk_emb em1 un1
            (fun uu___ ->
               let uu___1 =
                 let uu___2 = let uu___3 = type_of ed in as_arg uu___3 in
                 let uu___3 =
                   let uu___4 = let uu___5 = type_of ec in as_arg uu___5 in
                   let uu___5 =
                     let uu___6 = let uu___7 = type_of eb in as_arg uu___7 in
                     let uu___7 =
                       let uu___8 = let uu___9 = type_of ea in as_arg uu___9 in
                       [uu___8] in
                     uu___6 :: uu___7 in
                   uu___4 :: uu___5 in
                 uu___2 :: uu___3 in
               lid_as_typ FStarC_Parser_Const.lid_tuple4
                 [FStarC_Syntax_Syntax.U_zero;
                 FStarC_Syntax_Syntax.U_zero;
                 FStarC_Syntax_Syntax.U_zero;
                 FStarC_Syntax_Syntax.U_zero] uu___1) etyp
let e_tuple5 :
  'a 'b 'c 'd 'e .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          'd embedding -> 'e embedding -> ('a * 'b * 'c * 'd * 'e) embedding
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          fun ee ->
            let etyp uu___ =
              let uu___1 =
                let uu___2 =
                  FStarC_Ident.string_of_lid FStarC_Parser_Const.lid_tuple5 in
                let uu___3 =
                  let uu___4 = ea.e_typ () in
                  let uu___5 =
                    let uu___6 = eb.e_typ () in
                    let uu___7 =
                      let uu___8 = ec.e_typ () in
                      let uu___9 =
                        let uu___10 = ed.e_typ () in
                        let uu___11 = let uu___12 = ee.e_typ () in [uu___12] in
                        uu___10 :: uu___11 in
                      uu___8 :: uu___9 in
                    uu___6 :: uu___7 in
                  uu___4 :: uu___5 in
                (uu___2, uu___3) in
              FStarC_Syntax_Syntax.ET_app uu___1 in
            let em1 cb uu___ =
              match uu___ with
              | (x1, x2, x3, x4, x5) ->
                  lazy_embed etyp (x1, x2, x3, x4, x5)
                    (fun uu___1 ->
                       let uu___2 =
                         let uu___3 =
                           let uu___4 = embed ee cb x5 in as_arg uu___4 in
                         let uu___4 =
                           let uu___5 =
                             let uu___6 = embed ed cb x4 in as_arg uu___6 in
                           let uu___6 =
                             let uu___7 =
                               let uu___8 = embed ec cb x3 in as_arg uu___8 in
                             let uu___8 =
                               let uu___9 =
                                 let uu___10 = embed eb cb x2 in
                                 as_arg uu___10 in
                               let uu___10 =
                                 let uu___11 =
                                   let uu___12 = embed ea cb x1 in
                                   as_arg uu___12 in
                                 let uu___12 =
                                   let uu___13 =
                                     let uu___14 = type_of ee in
                                     as_iarg uu___14 in
                                   let uu___14 =
                                     let uu___15 =
                                       let uu___16 = type_of ed in
                                       as_iarg uu___16 in
                                     let uu___16 =
                                       let uu___17 =
                                         let uu___18 = type_of ec in
                                         as_iarg uu___18 in
                                       let uu___18 =
                                         let uu___19 =
                                           let uu___20 = type_of eb in
                                           as_iarg uu___20 in
                                         let uu___20 =
                                           let uu___21 =
                                             let uu___22 = type_of ea in
                                             as_iarg uu___22 in
                                           [uu___21] in
                                         uu___19 :: uu___20 in
                                       uu___17 :: uu___18 in
                                     uu___15 :: uu___16 in
                                   uu___13 :: uu___14 in
                                 uu___11 :: uu___12 in
                               uu___9 :: uu___10 in
                             uu___7 :: uu___8 in
                           uu___5 :: uu___6 in
                         uu___3 :: uu___4 in
                       lid_as_constr FStarC_Parser_Const.lid_Mktuple5
                         [FStarC_Syntax_Syntax.U_zero;
                         FStarC_Syntax_Syntax.U_zero;
                         FStarC_Syntax_Syntax.U_zero;
                         FStarC_Syntax_Syntax.U_zero;
                         FStarC_Syntax_Syntax.U_zero] uu___2) in
            let un1 cb trm =
              lazy_unembed etyp trm
                (fun uu___ ->
                   (fun trm1 ->
                      match trm1.nbe_t with
                      | Construct
                          (fvar, us,
                           (e1, uu___)::(d1, uu___1)::(c1, uu___2)::(b1,
                                                                    uu___3)::
                           (a1, uu___4)::uu___5::uu___6::uu___7::uu___8::uu___9::[])
                          when
                          FStarC_Syntax_Syntax.fv_eq_lid fvar
                            FStarC_Parser_Const.lid_Mktuple5
                          ->
                          Obj.magic
                            (Obj.repr
                               (let uu___10 = unembed ea cb a1 in
                                FStarC_Class_Monad.op_let_Bang
                                  FStarC_Class_Monad.monad_option () ()
                                  (Obj.magic uu___10)
                                  (fun uu___11 ->
                                     (fun a2 ->
                                        let a2 = Obj.magic a2 in
                                        let uu___11 = unembed eb cb b1 in
                                        Obj.magic
                                          (FStarC_Class_Monad.op_let_Bang
                                             FStarC_Class_Monad.monad_option
                                             () () (Obj.magic uu___11)
                                             (fun uu___12 ->
                                                (fun b2 ->
                                                   let b2 = Obj.magic b2 in
                                                   let uu___12 =
                                                     unembed ec cb c1 in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_let_Bang
                                                        FStarC_Class_Monad.monad_option
                                                        () ()
                                                        (Obj.magic uu___12)
                                                        (fun uu___13 ->
                                                           (fun c2 ->
                                                              let c2 =
                                                                Obj.magic c2 in
                                                              let uu___13 =
                                                                unembed ed cb
                                                                  d1 in
                                                              Obj.magic
                                                                (FStarC_Class_Monad.op_let_Bang
                                                                   FStarC_Class_Monad.monad_option
                                                                   () ()
                                                                   (Obj.magic
                                                                    uu___13)
                                                                   (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun d2
                                                                    ->
                                                                    let d2 =
                                                                    Obj.magic
                                                                    d2 in
                                                                    let uu___14
                                                                    =
                                                                    unembed
                                                                    ee cb e1 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.op_let_Bang
                                                                    FStarC_Class_Monad.monad_option
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun e2
                                                                    ->
                                                                    let e2 =
                                                                    Obj.magic
                                                                    e2 in
                                                                    Obj.magic
                                                                    (FStar_Pervasives_Native.Some
                                                                    (a2, b2,
                                                                    c2, d2,
                                                                    e2)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                             uu___13)))
                                                  uu___12))) uu___11)))
                      | uu___ ->
                          Obj.magic (Obj.repr FStar_Pervasives_Native.None))
                     uu___) in
            mk_emb em1 un1
              (fun uu___ ->
                 let uu___1 =
                   let uu___2 = let uu___3 = type_of ee in as_arg uu___3 in
                   let uu___3 =
                     let uu___4 = let uu___5 = type_of ed in as_arg uu___5 in
                     let uu___5 =
                       let uu___6 = let uu___7 = type_of ec in as_arg uu___7 in
                       let uu___7 =
                         let uu___8 =
                           let uu___9 = type_of eb in as_arg uu___9 in
                         let uu___9 =
                           let uu___10 =
                             let uu___11 = type_of ea in as_arg uu___11 in
                           [uu___10] in
                         uu___8 :: uu___9 in
                       uu___6 :: uu___7 in
                     uu___4 :: uu___5 in
                   uu___2 :: uu___3 in
                 lid_as_typ FStarC_Parser_Const.lid_tuple5
                   [FStarC_Syntax_Syntax.U_zero;
                   FStarC_Syntax_Syntax.U_zero;
                   FStarC_Syntax_Syntax.U_zero;
                   FStarC_Syntax_Syntax.U_zero;
                   FStarC_Syntax_Syntax.U_zero] uu___1) etyp
let e_either :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a, 'b) FStar_Pervasives.either embedding
  =
  fun ea ->
    fun eb ->
      let etyp uu___ =
        let uu___1 =
          let uu___2 =
            FStarC_Ident.string_of_lid FStarC_Parser_Const.either_lid in
          let uu___3 =
            let uu___4 = ea.e_typ () in
            let uu___5 = let uu___6 = eb.e_typ () in [uu___6] in uu___4 ::
              uu___5 in
          (uu___2, uu___3) in
        FStarC_Syntax_Syntax.ET_app uu___1 in
      let em1 cb s =
        lazy_embed etyp s
          (fun uu___ ->
             match s with
             | FStar_Pervasives.Inl a1 ->
                 let uu___1 =
                   let uu___2 = let uu___3 = embed ea cb a1 in as_arg uu___3 in
                   let uu___3 =
                     let uu___4 = let uu___5 = type_of eb in as_iarg uu___5 in
                     let uu___5 =
                       let uu___6 = let uu___7 = type_of ea in as_iarg uu___7 in
                       [uu___6] in
                     uu___4 :: uu___5 in
                   uu___2 :: uu___3 in
                 lid_as_constr FStarC_Parser_Const.inl_lid
                   [FStarC_Syntax_Syntax.U_zero; FStarC_Syntax_Syntax.U_zero]
                   uu___1
             | FStar_Pervasives.Inr b1 ->
                 let uu___1 =
                   let uu___2 = let uu___3 = embed eb cb b1 in as_arg uu___3 in
                   let uu___3 =
                     let uu___4 = let uu___5 = type_of eb in as_iarg uu___5 in
                     let uu___5 =
                       let uu___6 = let uu___7 = type_of ea in as_iarg uu___7 in
                       [uu___6] in
                     uu___4 :: uu___5 in
                   uu___2 :: uu___3 in
                 lid_as_constr FStarC_Parser_Const.inr_lid
                   [FStarC_Syntax_Syntax.U_zero; FStarC_Syntax_Syntax.U_zero]
                   uu___1) in
      let un1 cb trm =
        lazy_unembed etyp trm
          (fun trm1 ->
             match trm1.nbe_t with
             | Construct (fvar, us, (a1, uu___)::uu___1::uu___2::[]) when
                 FStarC_Syntax_Syntax.fv_eq_lid fvar
                   FStarC_Parser_Const.inl_lid
                 ->
                 let uu___3 = unembed ea cb a1 in
                 FStarC_Compiler_Util.bind_opt uu___3
                   (fun a2 ->
                      FStar_Pervasives_Native.Some (FStar_Pervasives.Inl a2))
             | Construct (fvar, us, (b1, uu___)::uu___1::uu___2::[]) when
                 FStarC_Syntax_Syntax.fv_eq_lid fvar
                   FStarC_Parser_Const.inr_lid
                 ->
                 let uu___3 = unembed eb cb b1 in
                 FStarC_Compiler_Util.bind_opt uu___3
                   (fun b2 ->
                      FStar_Pervasives_Native.Some (FStar_Pervasives.Inr b2))
             | uu___ -> FStar_Pervasives_Native.None) in
      mk_emb em1 un1
        (fun uu___ ->
           let uu___1 =
             let uu___2 = let uu___3 = type_of eb in as_arg uu___3 in
             let uu___3 =
               let uu___4 = let uu___5 = type_of ea in as_arg uu___5 in
               [uu___4] in
             uu___2 :: uu___3 in
           lid_as_typ FStarC_Parser_Const.either_lid
             [FStarC_Syntax_Syntax.U_zero; FStarC_Syntax_Syntax.U_zero]
             uu___1) etyp
let (e___range : FStarC_Compiler_Range_Type.range embedding) =
  let em1 cb r = Constant (Range r) in
  let un1 cb t1 =
    match t1 with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu___ -> FStar_Pervasives_Native.None in
  mk_emb' em1 un1
    (fun uu___ -> lid_as_typ FStarC_Parser_Const.__range_lid [] [])
    (FStarC_Syntax_Embeddings_Base.emb_typ_of
       FStarC_Syntax_Embeddings.e_range)
let e_sealed :
  'a . 'a embedding -> 'a FStarC_Compiler_Sealed.sealed embedding =
  fun ea ->
    let etyp uu___ =
      let uu___1 =
        let uu___2 =
          FStarC_Ident.string_of_lid FStarC_Parser_Const.sealed_lid in
        let uu___3 = let uu___4 = ea.e_typ () in [uu___4] in (uu___2, uu___3) in
      FStarC_Syntax_Syntax.ET_app uu___1 in
    let em1 cb x =
      lazy_embed etyp x
        (fun uu___ ->
           let uu___1 =
             let uu___2 =
               let uu___3 = embed ea cb (FStarC_Compiler_Sealed.unseal x) in
               as_arg uu___3 in
             let uu___3 =
               let uu___4 = let uu___5 = type_of ea in as_iarg uu___5 in
               [uu___4] in
             uu___2 :: uu___3 in
           lid_as_constr FStarC_Parser_Const.seal_lid
             [FStarC_Syntax_Syntax.U_zero] uu___1) in
    let un1 cb trm =
      lazy_unembed etyp trm
        (fun uu___ ->
           (fun trm1 ->
              match trm1.nbe_t with
              | Construct (fvar, us, (a1, uu___)::uu___1::[]) when
                  FStarC_Syntax_Syntax.fv_eq_lid fvar
                    FStarC_Parser_Const.seal_lid
                  ->
                  Obj.magic
                    (Obj.repr
                       (let uu___2 = unembed ea cb a1 in
                        FStarC_Class_Monad.fmap
                          FStarC_Class_Monad.monad_option () ()
                          (fun uu___3 ->
                             (Obj.magic FStarC_Compiler_Sealed.seal) uu___3)
                          (Obj.magic uu___2)))
              | uu___ -> Obj.magic (Obj.repr FStar_Pervasives_Native.None))
             uu___) in
    mk_emb em1 un1
      (fun uu___ ->
         let uu___1 =
           let uu___2 = let uu___3 = type_of ea in as_arg uu___3 in [uu___2] in
         lid_as_typ FStarC_Parser_Const.sealed_lid
           [FStarC_Syntax_Syntax.U_zero] uu___1) etyp
let (e_range : FStarC_Compiler_Range_Type.range embedding) =
  embed_as (e_sealed e___range) FStarC_Compiler_Sealed.unseal
    FStarC_Compiler_Sealed.seal FStar_Pervasives_Native.None
let (e_issue : FStarC_Errors.issue embedding) =
  let t_issue =
    FStarC_Syntax_Embeddings_Base.type_of FStarC_Syntax_Embeddings.e_issue in
  let li blob rng =
    let uu___ = FStarC_Dyn.mkdyn blob in
    {
      FStarC_Syntax_Syntax.blob = uu___;
      FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_issue;
      FStarC_Syntax_Syntax.ltyp = t_issue;
      FStarC_Syntax_Syntax.rng = rng
    } in
  let em1 cb iss =
    let uu___ =
      let uu___1 =
        let uu___2 = li iss FStarC_Compiler_Range_Type.dummyRange in
        FStar_Pervasives.Inl uu___2 in
      let uu___2 =
        FStarC_Thunk.mk (fun uu___3 -> failwith "Cannot unembed issue") in
      (uu___1, uu___2) in
    Lazy uu___ in
  let un1 cb t1 =
    match t1 with
    | Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = blob;
           FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_issue;
           FStarC_Syntax_Syntax.ltyp = uu___;
           FStarC_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStarC_Dyn.undyn blob in
        FStar_Pervasives_Native.Some uu___3
    | uu___ -> FStar_Pervasives_Native.None in
  mk_emb' em1 un1
    (fun uu___ -> lid_as_typ FStarC_Parser_Const.issue_lid [] [])
    (FStarC_Syntax_Embeddings_Base.emb_typ_of
       FStarC_Syntax_Embeddings.e_issue)
let (e_document : FStarC_Pprint.document embedding) =
  let t_document =
    FStarC_Syntax_Embeddings_Base.type_of FStarC_Syntax_Embeddings.e_document in
  let li blob rng =
    let uu___ = FStarC_Dyn.mkdyn blob in
    {
      FStarC_Syntax_Syntax.blob = uu___;
      FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_doc;
      FStarC_Syntax_Syntax.ltyp = t_document;
      FStarC_Syntax_Syntax.rng = rng
    } in
  let em1 cb doc =
    let uu___ =
      let uu___1 =
        let uu___2 = li doc FStarC_Compiler_Range_Type.dummyRange in
        FStar_Pervasives.Inl uu___2 in
      let uu___2 =
        FStarC_Thunk.mk (fun uu___3 -> failwith "Cannot unembed document") in
      (uu___1, uu___2) in
    Lazy uu___ in
  let un1 cb t1 =
    match t1 with
    | Lazy
        (FStar_Pervasives.Inl
         { FStarC_Syntax_Syntax.blob = blob;
           FStarC_Syntax_Syntax.lkind = FStarC_Syntax_Syntax.Lazy_doc;
           FStarC_Syntax_Syntax.ltyp = uu___;
           FStarC_Syntax_Syntax.rng = uu___1;_},
         uu___2)
        ->
        let uu___3 = FStarC_Dyn.undyn blob in
        FStar_Pervasives_Native.Some uu___3
    | uu___ -> FStar_Pervasives_Native.None in
  mk_emb' em1 un1
    (fun uu___ -> lid_as_typ FStarC_Parser_Const.document_lid [] [])
    (FStarC_Syntax_Embeddings_Base.emb_typ_of
       FStarC_Syntax_Embeddings.e_document)
let (e_vconfig : FStarC_VConfig.vconfig embedding) =
  let em1 cb r = failwith "e_vconfig NBE" in
  let un1 cb t1 = failwith "e_vconfig NBE" in
  mk_emb' em1 un1
    (fun uu___ -> lid_as_typ FStarC_Parser_Const.vconfig_lid [] [])
    (FStarC_Syntax_Embeddings_Base.emb_typ_of
       FStarC_Syntax_Embeddings.e_vconfig)
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea ->
    let etyp uu___ =
      let uu___1 =
        let uu___2 = FStarC_Ident.string_of_lid FStarC_Parser_Const.list_lid in
        let uu___3 = let uu___4 = ea.e_typ () in [uu___4] in (uu___2, uu___3) in
      FStarC_Syntax_Syntax.ET_app uu___1 in
    let em1 cb l =
      lazy_embed etyp l
        (fun uu___ ->
           let typ1 = let uu___1 = type_of ea in as_iarg uu___1 in
           let nil =
             lid_as_constr FStarC_Parser_Const.nil_lid
               [FStarC_Syntax_Syntax.U_zero] [typ1] in
           let cons hd tl =
             let uu___1 =
               let uu___2 = as_arg tl in
               let uu___3 =
                 let uu___4 = let uu___5 = embed ea cb hd in as_arg uu___5 in
                 [uu___4; typ1] in
               uu___2 :: uu___3 in
             lid_as_constr FStarC_Parser_Const.cons_lid
               [FStarC_Syntax_Syntax.U_zero] uu___1 in
           FStarC_Compiler_List.fold_right cons l nil) in
    let rec un1 cb trm =
      lazy_unembed etyp trm
        (fun trm1 ->
           match trm1.nbe_t with
           | Construct (fv, uu___, uu___1) when
               FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.nil_lid
               -> FStar_Pervasives_Native.Some []
           | Construct
               (fv, uu___,
                (tl, FStar_Pervasives_Native.None)::(hd,
                                                     FStar_Pervasives_Native.None)::
                (uu___1, FStar_Pervasives_Native.Some
                 { FStarC_Syntax_Syntax.aqual_implicit = true;
                   FStarC_Syntax_Syntax.aqual_attributes = uu___2;_})::[])
               when
               FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.cons_lid
               ->
               let uu___3 = unembed ea cb hd in
               FStarC_Compiler_Util.bind_opt uu___3
                 (fun hd1 ->
                    let uu___4 = un1 cb tl in
                    FStarC_Compiler_Util.bind_opt uu___4
                      (fun tl1 -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | Construct
               (fv, uu___,
                (tl, FStar_Pervasives_Native.None)::(hd,
                                                     FStar_Pervasives_Native.None)::[])
               when
               FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.cons_lid
               ->
               let uu___1 = unembed ea cb hd in
               FStarC_Compiler_Util.bind_opt uu___1
                 (fun hd1 ->
                    let uu___2 = un1 cb tl in
                    FStarC_Compiler_Util.bind_opt uu___2
                      (fun tl1 -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | uu___ -> FStar_Pervasives_Native.None) in
    mk_emb em1 un1
      (fun uu___ ->
         let uu___1 =
           let uu___2 = let uu___3 = type_of ea in as_arg uu___3 in [uu___2] in
         lid_as_typ FStarC_Parser_Const.list_lid
           [FStarC_Syntax_Syntax.U_zero] uu___1) etyp
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea ->
    fun eb ->
      let etyp uu___ =
        let uu___1 =
          let uu___2 = ea.e_typ () in
          let uu___3 = eb.e_typ () in (uu___2, uu___3) in
        FStarC_Syntax_Syntax.ET_fun uu___1 in
      let em1 cb f =
        lazy_embed etyp f
          (fun uu___ ->
             let uu___1 =
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 = let uu___6 = type_of eb in as_arg uu___6 in
                     [uu___5] in
                   Lam_args uu___4 in
                 {
                   interp =
                     (fun tas ->
                        let uu___4 =
                          let uu___5 =
                            let uu___6 = FStarC_Compiler_List.hd tas in
                            FStar_Pervasives_Native.fst uu___6 in
                          unembed ea cb uu___5 in
                        match uu___4 with
                        | FStar_Pervasives_Native.Some a1 ->
                            let uu___5 = f a1 in embed eb cb uu___5
                        | FStar_Pervasives_Native.None ->
                            failwith "cannot unembed function argument");
                   shape = uu___3;
                   arity = Prims.int_one
                 } in
               Lam uu___2 in
             mk_t uu___1) in
      let un1 cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x ->
               let uu___ =
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = let uu___4 = embed ea cb x in as_arg uu___4 in
                     [uu___3] in
                   cb.iapp lam1 uu___2 in
                 unembed eb cb uu___1 in
               match uu___ with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None ->
                   failwith "cannot unembed function result") in
        lazy_unembed etyp lam k in
      mk_emb em1 un1
        (fun uu___ ->
           let uu___1 = type_of ea in
           let uu___2 = let uu___3 = type_of eb in as_iarg uu___3 in
           make_arrow1 uu___1 uu___2) etyp
let (e_abstract_nbe_term : abstract_nbe_term embedding) =
  embed_as e_any (fun x -> AbstractNBE x)
    (fun x -> match x with | AbstractNBE x1 -> x1)
    FStar_Pervasives_Native.None
let e_unsupported : 'a . unit -> 'a embedding =
  fun uu___ ->
    let em1 _cb a1 = failwith "Unsupported NBE embedding" in
    let un1 _cb t1 = failwith "Unsupported NBE embedding" in
    mk_emb em1 un1
      (fun uu___1 -> lid_as_typ FStarC_Parser_Const.term_lid [] [])
      (fun uu___1 -> FStarC_Syntax_Syntax.ET_abstract)
let (e_norm_step : FStar_Pervasives.norm_step embedding) =
  let em1 cb n =
    match n with
    | FStar_Pervasives.Simpl ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.steps_simpl
            FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Pervasives.Weak ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.steps_weak
            FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Pervasives.HNF ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.steps_hnf
            FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Pervasives.Primops ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.steps_primops
            FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Pervasives.Delta ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.steps_delta
            FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Pervasives.Zeta ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.steps_zeta
            FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Pervasives.Iota ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.steps_iota
            FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Pervasives.Reify ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.steps_reify
            FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Pervasives.NBE ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.steps_nbe
            FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Pervasives.UnfoldOnly l ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.steps_unfoldonly
            FStar_Pervasives_Native.None in
        let uu___1 =
          let uu___2 =
            let uu___3 = embed (e_list e_string) cb l in as_arg uu___3 in
          [uu___2] in
        mkFV uu___ [] uu___1
    | FStar_Pervasives.UnfoldFully l ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv
            FStarC_Parser_Const.steps_unfoldfully
            FStar_Pervasives_Native.None in
        let uu___1 =
          let uu___2 =
            let uu___3 = embed (e_list e_string) cb l in as_arg uu___3 in
          [uu___2] in
        mkFV uu___ [] uu___1
    | FStar_Pervasives.UnfoldAttr l ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.steps_unfoldattr
            FStar_Pervasives_Native.None in
        let uu___1 =
          let uu___2 =
            let uu___3 = embed (e_list e_string) cb l in as_arg uu___3 in
          [uu___2] in
        mkFV uu___ [] uu___1
    | FStar_Pervasives.UnfoldQual l ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.steps_unfoldqual
            FStar_Pervasives_Native.None in
        let uu___1 =
          let uu___2 =
            let uu___3 = embed (e_list e_string) cb l in as_arg uu___3 in
          [uu___2] in
        mkFV uu___ [] uu___1
    | FStar_Pervasives.UnfoldNamespace l ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv
            FStarC_Parser_Const.steps_unfoldnamespace
            FStar_Pervasives_Native.None in
        let uu___1 =
          let uu___2 =
            let uu___3 = embed (e_list e_string) cb l in as_arg uu___3 in
          [uu___2] in
        mkFV uu___ [] uu___1
    | FStar_Pervasives.ZetaFull ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.steps_zeta_full
            FStar_Pervasives_Native.None in
        mkFV uu___ [] []
    | FStar_Pervasives.Unascribe ->
        let uu___ =
          FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.steps_unascribe
            FStar_Pervasives_Native.None in
        mkFV uu___ [] [] in
  let un1 cb t0 =
    match t0.nbe_t with
    | FV (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Pervasives.Simpl
    | FV (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Pervasives.Weak
    | FV (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Pervasives.HNF
    | FV (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.steps_primops
        -> FStar_Pervasives_Native.Some FStar_Pervasives.Primops
    | FV (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Pervasives.Delta
    | FV (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Pervasives.Zeta
    | FV (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Pervasives.Iota
    | FV (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Pervasives.NBE
    | FV (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Pervasives.Reify
    | FV (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.steps_zeta_full
        -> FStar_Pervasives_Native.Some FStar_Pervasives.ZetaFull
    | FV (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv FStarC_Parser_Const.steps_unascribe
        -> FStar_Pervasives_Native.Some FStar_Pervasives.Unascribe
    | FV (fv, uu___, (l, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Parser_Const.steps_unfoldonly
        ->
        let uu___2 = unembed (e_list e_string) cb l in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun ss ->
             FStar_Pervasives_Native.Some (FStar_Pervasives.UnfoldOnly ss))
    | FV (fv, uu___, (l, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Parser_Const.steps_unfoldfully
        ->
        let uu___2 = unembed (e_list e_string) cb l in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun ss ->
             FStar_Pervasives_Native.Some (FStar_Pervasives.UnfoldFully ss))
    | FV (fv, uu___, (l, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Parser_Const.steps_unfoldattr
        ->
        let uu___2 = unembed (e_list e_string) cb l in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun ss ->
             FStar_Pervasives_Native.Some (FStar_Pervasives.UnfoldAttr ss))
    | FV (fv, uu___, (l, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Parser_Const.steps_unfoldqual
        ->
        let uu___2 = unembed (e_list e_string) cb l in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun ss ->
             FStar_Pervasives_Native.Some (FStar_Pervasives.UnfoldQual ss))
    | FV (fv, uu___, (l, uu___1)::[]) when
        FStarC_Syntax_Syntax.fv_eq_lid fv
          FStarC_Parser_Const.steps_unfoldnamespace
        ->
        let uu___2 = unembed (e_list e_string) cb l in
        FStarC_Compiler_Util.bind_opt uu___2
          (fun ss ->
             FStar_Pervasives_Native.Some
               (FStar_Pervasives.UnfoldNamespace ss))
    | uu___ ->
        ((let uu___2 =
            let uu___3 = t_to_string t0 in
            FStarC_Compiler_Util.format1 "Not an embedded norm_step: %s"
              uu___3 in
          FStarC_Errors.log_issue0 FStarC_Errors_Codes.Warning_NotEmbedded ()
            (Obj.magic FStarC_Errors_Msg.is_error_message_string)
            (Obj.magic uu___2));
         FStar_Pervasives_Native.None) in
  mk_emb em1 un1
    (fun uu___ ->
       let uu___1 =
         FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.norm_step_lid
           FStar_Pervasives_Native.None in
       mkFV uu___1 [] [])
    (FStarC_Syntax_Embeddings_Base.emb_typ_of
       FStarC_Syntax_Embeddings.e_norm_step)
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h -> fun _args -> h);
    translate = (fun uu___ -> failwith "bogus_cbs translate")
  }
let (arg_as_int : arg -> FStarC_BigInt.t FStar_Pervasives_Native.option) =
  fun a -> unembed e_int bogus_cbs (FStar_Pervasives_Native.fst a)
let (arg_as_bool : arg -> Prims.bool FStar_Pervasives_Native.option) =
  fun a -> unembed e_bool bogus_cbs (FStar_Pervasives_Native.fst a)
let arg_as_list :
  'a . 'a embedding -> arg -> 'a Prims.list FStar_Pervasives_Native.option =
  fun e ->
    fun a1 -> unembed (e_list e) bogus_cbs (FStar_Pervasives_Native.fst a1)
let lift_unary :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun aopts ->
      match aopts with
      | (FStar_Pervasives_Native.Some a1)::[] ->
          let uu___ = f a1 in FStar_Pervasives_Native.Some uu___
      | uu___ -> FStar_Pervasives_Native.None
let lift_binary :
  'a 'b .
    ('a -> 'a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f ->
    fun aopts ->
      match aopts with
      | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
          a1)::[] ->
          let uu___ = f a0 a1 in FStar_Pervasives_Native.Some uu___
      | uu___ -> FStar_Pervasives_Native.None
let mixed_binary_op :
  'a 'b 'c .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      (arg -> 'b FStar_Pervasives_Native.option) ->
        ('c -> t) ->
          (FStarC_Syntax_Syntax.universes ->
             'a -> 'b -> 'c FStar_Pervasives_Native.option)
            ->
            FStarC_Syntax_Syntax.universes ->
              args -> t FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun as_b ->
      fun embed_c ->
        fun f ->
          fun us ->
            fun args1 ->
              match args1 with
              | a1::b1::[] ->
                  let uu___ =
                    let uu___1 = as_a a1 in
                    let uu___2 = as_b b1 in (uu___1, uu___2) in
                  (match uu___ with
                   | (FStar_Pervasives_Native.Some a2,
                      FStar_Pervasives_Native.Some b2) ->
                       let uu___1 = f us a2 b2 in
                       (match uu___1 with
                        | FStar_Pervasives_Native.Some c1 ->
                            let uu___2 = embed_c c1 in
                            FStar_Pervasives_Native.Some uu___2
                        | uu___2 -> FStar_Pervasives_Native.None)
                   | uu___1 -> FStar_Pervasives_Native.None)
              | uu___ -> FStar_Pervasives_Native.None
let mixed_ternary_op :
  'a 'b 'c 'd .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      (arg -> 'b FStar_Pervasives_Native.option) ->
        (arg -> 'c FStar_Pervasives_Native.option) ->
          ('d -> t) ->
            (FStarC_Syntax_Syntax.universes ->
               'a -> 'b -> 'c -> 'd FStar_Pervasives_Native.option)
              ->
              FStarC_Syntax_Syntax.universes ->
                args -> t FStar_Pervasives_Native.option
  =
  fun as_a ->
    fun as_b ->
      fun as_c ->
        fun embed_d ->
          fun f ->
            fun us ->
              fun args1 ->
                match args1 with
                | a1::b1::c1::[] ->
                    let uu___ =
                      let uu___1 = as_a a1 in
                      let uu___2 = as_b b1 in
                      let uu___3 = as_c c1 in (uu___1, uu___2, uu___3) in
                    (match uu___ with
                     | (FStar_Pervasives_Native.Some a2,
                        FStar_Pervasives_Native.Some b2,
                        FStar_Pervasives_Native.Some c2) ->
                         let uu___1 = f us a2 b2 c2 in
                         (match uu___1 with
                          | FStar_Pervasives_Native.Some d1 ->
                              let uu___2 = embed_d d1 in
                              FStar_Pervasives_Native.Some uu___2
                          | uu___2 -> FStar_Pervasives_Native.None)
                     | uu___1 -> FStar_Pervasives_Native.None)
                | uu___ -> FStar_Pervasives_Native.None
let (dummy_interp :
  FStarC_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid ->
    fun args1 ->
      let uu___ =
        let uu___1 = FStarC_Ident.string_of_lid lid in
        Prims.strcat "No interpretation for " uu___1 in
      failwith uu___
let (and_op : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu___ = arg_as_bool a1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some (false) ->
             let uu___1 = embed e_bool bogus_cbs false in
             FStar_Pervasives_Native.Some uu___1
         | FStar_Pervasives_Native.Some (true) ->
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst a2)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments"
let (or_op : args -> t FStar_Pervasives_Native.option) =
  fun args1 ->
    match args1 with
    | a1::a2::[] ->
        let uu___ = arg_as_bool a1 in
        (match uu___ with
         | FStar_Pervasives_Native.Some (true) ->
             let uu___1 = embed e_bool bogus_cbs true in
             FStar_Pervasives_Native.Some uu___1
         | FStar_Pervasives_Native.Some (false) ->
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst a2)
         | uu___1 -> FStar_Pervasives_Native.None)
    | uu___ -> failwith "Unexpected number of arguments"
let arrow_as_prim_step_1 :
  'a 'b .
    'a embedding ->
      'b embedding ->
        ('a -> 'b) ->
          FStarC_Ident.lid ->
            nbe_cbs ->
              FStarC_Syntax_Syntax.universes ->
                args -> t FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun f ->
        fun _fv_lid ->
          fun cb ->
            let f_wrapped _us args1 =
              let uu___ = FStarC_Compiler_List.hd args1 in
              match uu___ with
              | (x, uu___1) ->
                  let uu___2 = unembed ea cb x in
                  FStarC_Compiler_Util.map_opt uu___2
                    (fun x1 -> let uu___3 = f x1 in embed eb cb uu___3) in
            f_wrapped
let arrow_as_prim_step_2 :
  'a 'b 'c .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          ('a -> 'b -> 'c) ->
            FStarC_Ident.lid ->
              nbe_cbs ->
                FStarC_Syntax_Syntax.universes ->
                  args -> t FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun f ->
          fun _fv_lid ->
            fun cb ->
              let f_wrapped _us args1 =
                let uu___ = FStarC_Compiler_List.hd args1 in
                match uu___ with
                | (x, uu___1) ->
                    let uu___2 =
                      let uu___3 = FStarC_Compiler_List.tl args1 in
                      FStarC_Compiler_List.hd uu___3 in
                    (match uu___2 with
                     | (y, uu___3) ->
                         let uu___4 = unembed ea cb x in
                         FStarC_Compiler_Util.bind_opt uu___4
                           (fun x1 ->
                              let uu___5 = unembed eb cb y in
                              FStarC_Compiler_Util.bind_opt uu___5
                                (fun y1 ->
                                   let uu___6 =
                                     let uu___7 = f x1 y1 in
                                     embed ec cb uu___7 in
                                   FStar_Pervasives_Native.Some uu___6))) in
              f_wrapped
let arrow_as_prim_step_3 :
  'a 'b 'c 'd .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          'd embedding ->
            ('a -> 'b -> 'c -> 'd) ->
              FStarC_Ident.lid ->
                nbe_cbs ->
                  FStarC_Syntax_Syntax.universes ->
                    args -> t FStar_Pervasives_Native.option
  =
  fun ea ->
    fun eb ->
      fun ec ->
        fun ed ->
          fun f ->
            fun _fv_lid ->
              fun cb ->
                let f_wrapped _us args1 =
                  let uu___ = FStarC_Compiler_List.hd args1 in
                  match uu___ with
                  | (x, uu___1) ->
                      let uu___2 =
                        let uu___3 = FStarC_Compiler_List.tl args1 in
                        FStarC_Compiler_List.hd uu___3 in
                      (match uu___2 with
                       | (y, uu___3) ->
                           let uu___4 =
                             let uu___5 =
                               let uu___6 = FStarC_Compiler_List.tl args1 in
                               FStarC_Compiler_List.tl uu___6 in
                             FStarC_Compiler_List.hd uu___5 in
                           (match uu___4 with
                            | (z, uu___5) ->
                                let uu___6 = unembed ea cb x in
                                FStarC_Compiler_Util.bind_opt uu___6
                                  (fun x1 ->
                                     let uu___7 = unembed eb cb y in
                                     FStarC_Compiler_Util.bind_opt uu___7
                                       (fun y1 ->
                                          let uu___8 = unembed ec cb z in
                                          FStarC_Compiler_Util.bind_opt
                                            uu___8
                                            (fun z1 ->
                                               let uu___9 =
                                                 let uu___10 = f x1 y1 z1 in
                                                 embed ed cb uu___10 in
                                               FStar_Pervasives_Native.Some
                                                 uu___9))))) in
                f_wrapped
let (e_order : FStar_Order.order embedding) =
  let ord_Lt_lid =
    FStarC_Ident.lid_of_path ["FStar"; "Order"; "Lt"]
      FStarC_Compiler_Range_Type.dummyRange in
  let ord_Eq_lid =
    FStarC_Ident.lid_of_path ["FStar"; "Order"; "Eq"]
      FStarC_Compiler_Range_Type.dummyRange in
  let ord_Gt_lid =
    FStarC_Ident.lid_of_path ["FStar"; "Order"; "Gt"]
      FStarC_Compiler_Range_Type.dummyRange in
  let ord_Lt = FStarC_Syntax_Syntax.tdataconstr ord_Lt_lid in
  let ord_Eq = FStarC_Syntax_Syntax.tdataconstr ord_Eq_lid in
  let ord_Gt = FStarC_Syntax_Syntax.tdataconstr ord_Gt_lid in
  let ord_Lt_fv =
    FStarC_Syntax_Syntax.lid_as_fv ord_Lt_lid
      (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor) in
  let ord_Eq_fv =
    FStarC_Syntax_Syntax.lid_as_fv ord_Eq_lid
      (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor) in
  let ord_Gt_fv =
    FStarC_Syntax_Syntax.lid_as_fv ord_Gt_lid
      (FStar_Pervasives_Native.Some FStarC_Syntax_Syntax.Data_ctor) in
  let embed_order cb o =
    match o with
    | FStar_Order.Lt -> mkConstruct ord_Lt_fv [] []
    | FStar_Order.Eq -> mkConstruct ord_Eq_fv [] []
    | FStar_Order.Gt -> mkConstruct ord_Gt_fv [] [] in
  let unembed_order cb t1 =
    match t1.nbe_t with
    | Construct (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv ord_Lt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Lt
    | Construct (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv ord_Eq_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Eq
    | Construct (fv, uu___, []) when
        FStarC_Syntax_Syntax.fv_eq_lid fv ord_Gt_lid ->
        FStar_Pervasives_Native.Some FStar_Order.Gt
    | uu___ -> FStar_Pervasives_Native.None in
  let fv_as_emb_typ fv =
    let uu___ =
      let uu___1 =
        FStarC_Ident.string_of_lid
          (fv.FStarC_Syntax_Syntax.fv_name).FStarC_Syntax_Syntax.v in
      (uu___1, []) in
    FStarC_Syntax_Syntax.ET_app uu___ in
  let fv =
    FStarC_Syntax_Syntax.lid_as_fv FStarC_Parser_Const.order_lid
      FStar_Pervasives_Native.None in
  mk_emb embed_order unembed_order (fun uu___ -> mkFV fv [] [])
    (fun uu___ -> fv_as_emb_typ fv)