open Prims
type var = FStar_Syntax_Syntax.bv
type sort = Prims.int
type constant =
  | Unit 
  | Bool of Prims.bool 
  | Int of FStar_BigInt.t 
  | String of (Prims.string * FStar_Range.range) 
  | Char of FStar_Char.char 
  | Range of FStar_Range.range 
  | SConst of FStar_Const.sconst 
let (uu___is_Unit : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Unit  -> true | uu____64 -> false 
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____77 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Int _0 -> true | uu____99 -> false 
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____123 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____158 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____180 -> false
  
let (__proj__Range__item___0 : constant -> FStar_Range.range) =
  fun projectee  -> match projectee with | Range _0 -> _0 
let (uu___is_SConst : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | SConst _0 -> true | uu____199 -> false
  
let (__proj__SConst__item___0 : constant -> FStar_Const.sconst) =
  fun projectee  -> match projectee with | SConst _0 -> _0 
type atom =
  | Var of var 
  | Match of (t * (unit -> FStar_Syntax_Syntax.branch Prims.list)) 
  | UnreducedLet of (var * t FStar_Thunk.t * t FStar_Thunk.t * t
  FStar_Thunk.t * FStar_Syntax_Syntax.letbinding) 
  | UnreducedLetRec of ((var * t * t) Prims.list * t *
  FStar_Syntax_Syntax.letbinding Prims.list) 
  | UVar of FStar_Syntax_Syntax.term FStar_Thunk.t 
and t' =
  | Lam of ((t Prims.list -> t) *
  ((t Prims.list * FStar_Syntax_Syntax.binders *
     FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option),
  (t * FStar_Syntax_Syntax.aqual) Prims.list) FStar_Util.either * Prims.int)
  
  | Accu of (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | Construct of (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe
  Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | FV of (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list *
  (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | Constant of constant 
  | Type_t of FStar_Syntax_Syntax.universe 
  | Univ of FStar_Syntax_Syntax.universe 
  | Unknown 
  | Arrow of
  (FStar_Syntax_Syntax.term FStar_Thunk.t,((t * FStar_Syntax_Syntax.aqual)
                                            Prims.list * comp))
  FStar_Util.either 
  | Refinement of ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual))) 
  | Reflect of t 
  | Quote of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo) 
  | Lazy of
  ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                   FStar_Syntax_Syntax.emb_typ))
  FStar_Util.either * t FStar_Thunk.t) 
  | Meta of (t * FStar_Syntax_Syntax.metadata FStar_Thunk.t) 
  | TopLevelLet of (FStar_Syntax_Syntax.letbinding * Prims.int * (t *
  FStar_Syntax_Syntax.aqual) Prims.list) 
  | TopLevelRec of (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool
  Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | LocalLetRec of (Prims.int * FStar_Syntax_Syntax.letbinding *
  FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
  FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool Prims.list) 
and t = {
  nbe_t: t' ;
  nbe_r: FStar_Range.range }
and comp =
  | Tot of (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  
  | GTot of (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  
  | Comp of comp_typ 
and comp_typ =
  {
  comp_univs: FStar_Syntax_Syntax.universes ;
  effect_name: FStar_Ident.lident ;
  result_typ: t ;
  effect_args: (t * FStar_Syntax_Syntax.aqual) Prims.list ;
  flags: cflag Prims.list }
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
  | DECREASES of t 
and residual_comp =
  {
  residual_effect: FStar_Ident.lident ;
  residual_typ: t FStar_Pervasives_Native.option ;
  residual_flags: cflag Prims.list }
let (uu___is_Var : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____963 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____991 -> false
  
let (__proj__Match__item___0 :
  atom -> (t * (unit -> FStar_Syntax_Syntax.branch Prims.list))) =
  fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_UnreducedLet : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLet _0 -> true | uu____1053 -> false
  
let (__proj__UnreducedLet__item___0 :
  atom ->
    (var * t FStar_Thunk.t * t FStar_Thunk.t * t FStar_Thunk.t *
      FStar_Syntax_Syntax.letbinding))
  = fun projectee  -> match projectee with | UnreducedLet _0 -> _0 
let (uu___is_UnreducedLetRec : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLetRec _0 -> true | uu____1136 -> false
  
let (__proj__UnreducedLetRec__item___0 :
  atom ->
    ((var * t * t) Prims.list * t * FStar_Syntax_Syntax.letbinding
      Prims.list))
  = fun projectee  -> match projectee with | UnreducedLetRec _0 -> _0 
let (uu___is_UVar : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UVar _0 -> true | uu____1205 -> false
  
let (__proj__UVar__item___0 : atom -> FStar_Syntax_Syntax.term FStar_Thunk.t)
  = fun projectee  -> match projectee with | UVar _0 -> _0 
let (uu___is_Lam : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____1262 -> false
  
let (__proj__Lam__item___0 :
  t' ->
    ((t Prims.list -> t) *
      ((t Prims.list * FStar_Syntax_Syntax.binders *
         FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option),
      (t * FStar_Syntax_Syntax.aqual) Prims.list) FStar_Util.either *
      Prims.int))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____1387 -> false
  
let (__proj__Accu__item___0 :
  t' -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____1450 -> false
  
let (__proj__Construct__item___0 :
  t' ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____1525 -> false
  
let (__proj__FV__item___0 :
  t' ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____1586 -> false
  
let (__proj__Constant__item___0 : t' -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____1605 -> false
  
let (__proj__Type_t__item___0 : t' -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1624 -> false
  
let (__proj__Univ__item___0 : t' -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1642 -> false
  
let (uu___is_Arrow : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____1670 -> false
  
let (__proj__Arrow__item___0 :
  t' ->
    (FStar_Syntax_Syntax.term FStar_Thunk.t,((t * FStar_Syntax_Syntax.aqual)
                                              Prims.list * comp))
      FStar_Util.either)
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____1751 -> false
  
let (__proj__Refinement__item___0 :
  t' -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1812 -> false
  
let (__proj__Reflect__item___0 : t' -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1835 -> false
  
let (__proj__Quote__item___0 :
  t' -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1880 -> false
  
let (__proj__Lazy__item___0 :
  t' ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Thunk.t))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Meta : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | Meta _0 -> true | uu____1947 -> false
  
let (__proj__Meta__item___0 :
  t' -> (t * FStar_Syntax_Syntax.metadata FStar_Thunk.t)) =
  fun projectee  -> match projectee with | Meta _0 -> _0 
let (uu___is_TopLevelLet : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____1997 -> false
  
let (__proj__TopLevelLet__item___0 :
  t' ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | TopLevelLet _0 -> _0 
let (uu___is_TopLevelRec : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelRec _0 -> true | uu____2073 -> false
  
let (__proj__TopLevelRec__item___0 :
  t' ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool Prims.list * (t
      * FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | TopLevelRec _0 -> _0 
let (uu___is_LocalLetRec : t' -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalLetRec _0 -> true | uu____2175 -> false
  
let (__proj__LocalLetRec__item___0 :
  t' ->
    (Prims.int * FStar_Syntax_Syntax.letbinding *
      FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool
      Prims.list))
  = fun projectee  -> match projectee with | LocalLetRec _0 -> _0 
let (__proj__Mkt__item__nbe_t : t -> t') =
  fun projectee  -> match projectee with | { nbe_t; nbe_r;_} -> nbe_t 
let (__proj__Mkt__item__nbe_r : t -> FStar_Range.range) =
  fun projectee  -> match projectee with | { nbe_t; nbe_r;_} -> nbe_r 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____2303 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____2346 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____2383 -> false
  
let (__proj__Comp__item___0 : comp -> comp_typ) =
  fun projectee  -> match projectee with | Comp _0 -> _0 
let (__proj__Mkcomp_typ__item__comp_univs :
  comp_typ -> FStar_Syntax_Syntax.universes) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        comp_univs
  
let (__proj__Mkcomp_typ__item__effect_name : comp_typ -> FStar_Ident.lident)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        effect_name
  
let (__proj__Mkcomp_typ__item__result_typ : comp_typ -> t) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        result_typ
  
let (__proj__Mkcomp_typ__item__effect_args :
  comp_typ -> (t * FStar_Syntax_Syntax.aqual) Prims.list) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} ->
        effect_args
  
let (__proj__Mkcomp_typ__item__flags : comp_typ -> cflag Prims.list) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags;_} -> flags
  
let (uu___is_TOTAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | TOTAL  -> true | uu____2512 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____2523 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____2534 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____2545 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____2556 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____2567 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____2578 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____2589 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____2600 -> false 
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____2612 -> false
  
let (__proj__DECREASES__item___0 : cflag -> t) =
  fun projectee  -> match projectee with | DECREASES _0 -> _0 
let (__proj__Mkresidual_comp__item__residual_effect :
  residual_comp -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_effect
  
let (__proj__Mkresidual_comp__item__residual_typ :
  residual_comp -> t FStar_Pervasives_Native.option) =
  fun projectee  ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_typ
  
let (__proj__Mkresidual_comp__item__residual_flags :
  residual_comp -> cflag Prims.list) =
  fun projectee  ->
    match projectee with
    | { residual_effect; residual_typ; residual_flags;_} -> residual_flags
  
type arg = (t * FStar_Syntax_Syntax.aqual)
type args = (t * FStar_Syntax_Syntax.aqual) Prims.list
type head = t
type annot = t FStar_Pervasives_Native.option
let (isAccu : t -> Prims.bool) =
  fun trm  ->
    match trm.nbe_t with | Accu uu____2688 -> true | uu____2700 -> false
  
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x.nbe_t with
    | Accu (uu____2710,uu____2711) -> false
    | uu____2725 -> true
  
let (mk_rt : FStar_Range.range -> t' -> t) =
  fun r  -> fun t1  -> { nbe_t = t1; nbe_r = r } 
let (mk_t : t' -> t) = fun t1  -> mk_rt FStar_Range.dummyRange t1 
let (nbe_t_of_t : t -> t') = fun t1  -> t1.nbe_t 
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun i  ->
    fun us  -> fun ts  -> FStar_All.pipe_left mk_t (Construct (i, us, ts))
  
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun i  ->
    fun us  ->
      fun ts  ->
        let uu____2798 = FStar_Syntax_Syntax.range_of_fv i  in
        mk_rt uu____2798 (FV (i, us, ts))
  
let (mkAccuVar : var -> t) =
  fun v  ->
    let uu____2813 = FStar_Syntax_Syntax.range_of_bv v  in
    mk_rt uu____2813 (Accu ((Var v), []))
  
let (mkAccuMatch : t -> (unit -> FStar_Syntax_Syntax.branch Prims.list) -> t)
  =
  fun s  -> fun bs  -> FStar_All.pipe_left mk_t (Accu ((Match (s, bs)), [])) 
let (equal_if : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___0_2865  ->
    if uu___0_2865
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2876  ->
    if uu___1_2876
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.NotEqual
  
let (eq_inj :
  FStar_Syntax_Util.eq_result ->
    FStar_Syntax_Util.eq_result -> FStar_Syntax_Util.eq_result)
  =
  fun r1  ->
    fun r2  ->
      match (r1, r2) with
      | (FStar_Syntax_Util.Equal ,FStar_Syntax_Util.Equal ) ->
          FStar_Syntax_Util.Equal
      | (FStar_Syntax_Util.NotEqual ,uu____2892) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2893,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____2894) -> FStar_Syntax_Util.Unknown
      | (uu____2895,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____2912 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____2932),String (s2,uu____2934)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2947,uu____2948) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match ((t1.nbe_t), (t2.nbe_t)) with
      | (Lam uu____2984,Lam uu____2985) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____3078 = eq_atom a1 a2  in
          eq_and uu____3078 (fun uu____3080  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____3119 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____3119
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____3135 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____3192  ->
                        match uu____3192 with
                        | ((a1,uu____3206),(a2,uu____3208)) ->
                            let uu____3217 = eq_t a1 a2  in
                            eq_inj acc uu____3217) FStar_Syntax_Util.Equal)
                uu____3135))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____3258 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____3258
          then
            let uu____3261 =
              let uu____3262 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____3262  in
            eq_and uu____3261 (fun uu____3265  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____3272 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____3272
      | (Univ u1,Univ u2) ->
          let uu____3276 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____3276
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____3323 =
            let uu____3324 =
              let uu____3325 = t11 ()  in
              FStar_Pervasives_Native.fst uu____3325  in
            let uu____3330 =
              let uu____3331 = t21 ()  in
              FStar_Pervasives_Native.fst uu____3331  in
            eq_t uu____3324 uu____3330  in
          eq_and uu____3323
            (fun uu____3339  ->
               let uu____3340 =
                 let uu____3341 = mkAccuVar x  in r1 uu____3341  in
               let uu____3342 =
                 let uu____3343 = mkAccuVar x  in r2 uu____3343  in
               eq_t uu____3340 uu____3342)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____3344,uu____3345) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) ->
          let uu____3350 = FStar_Syntax_Syntax.bv_eq bv1 bv2  in
          equal_if uu____3350
      | (uu____3352,uu____3353) -> FStar_Syntax_Util.Unknown

and (eq_arg : arg -> arg -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      eq_t (FStar_Pervasives_Native.fst a1) (FStar_Pervasives_Native.fst a2)

and (eq_args : args -> args -> FStar_Syntax_Util.eq_result) =
  fun as1  ->
    fun as2  ->
      match (as1, as2) with
      | ([],[]) -> FStar_Syntax_Util.Equal
      | (x::xs,y::ys) ->
          let uu____3434 = eq_arg x y  in
          eq_and uu____3434 (fun uu____3436  -> eq_args xs ys)
      | (uu____3437,uu____3438) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____3485) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____3490 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____3490
    | SConst s -> FStar_Syntax_Print.const_to_string s
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x.nbe_t with
    | Lam (b,uu____3508,arity) ->
        let uu____3562 = FStar_Util.string_of_int arity  in
        FStar_Util.format1 "Lam (_, %s args)" uu____3562
    | Accu (a,l) ->
        let uu____3579 =
          let uu____3581 = atom_to_string a  in
          let uu____3583 =
            let uu____3585 =
              let uu____3587 =
                let uu____3589 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____3589  in
              FStar_String.op_Hat uu____3587 ")"  in
            FStar_String.op_Hat ") (" uu____3585  in
          FStar_String.op_Hat uu____3581 uu____3583  in
        FStar_String.op_Hat "Accu (" uu____3579
    | Construct (fv,us,l) ->
        let uu____3627 =
          let uu____3629 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3631 =
            let uu____3633 =
              let uu____3635 =
                let uu____3637 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3637  in
              let uu____3643 =
                let uu____3645 =
                  let uu____3647 =
                    let uu____3649 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3649  in
                  FStar_String.op_Hat uu____3647 "]"  in
                FStar_String.op_Hat "] [" uu____3645  in
              FStar_String.op_Hat uu____3635 uu____3643  in
            FStar_String.op_Hat ") [" uu____3633  in
          FStar_String.op_Hat uu____3629 uu____3631  in
        FStar_String.op_Hat "Construct (" uu____3627
    | FV (fv,us,l) ->
        let uu____3688 =
          let uu____3690 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3692 =
            let uu____3694 =
              let uu____3696 =
                let uu____3698 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3698  in
              let uu____3704 =
                let uu____3706 =
                  let uu____3708 =
                    let uu____3710 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3710  in
                  FStar_String.op_Hat uu____3708 "]"  in
                FStar_String.op_Hat "] [" uu____3706  in
              FStar_String.op_Hat uu____3696 uu____3704  in
            FStar_String.op_Hat ") [" uu____3694  in
          FStar_String.op_Hat uu____3690 uu____3692  in
        FStar_String.op_Hat "FV (" uu____3688
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____3732 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____3732
    | Type_t u ->
        let uu____3736 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____3736
    | Arrow uu____3739 -> "Arrow"
    | Refinement (f,t1) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t2 =
          let uu____3781 = t1 ()  in FStar_Pervasives_Native.fst uu____3781
           in
        let uu____3786 =
          let uu____3788 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____3790 =
            let uu____3792 =
              let uu____3794 = t_to_string t2  in
              let uu____3796 =
                let uu____3798 =
                  let uu____3800 =
                    let uu____3802 =
                      let uu____3803 = mkAccuVar x1  in f uu____3803  in
                    t_to_string uu____3802  in
                  FStar_String.op_Hat uu____3800 "}"  in
                FStar_String.op_Hat "{" uu____3798  in
              FStar_String.op_Hat uu____3794 uu____3796  in
            FStar_String.op_Hat ":" uu____3792  in
          FStar_String.op_Hat uu____3788 uu____3790  in
        FStar_String.op_Hat "Refinement " uu____3786
    | Unknown  -> "Unknown"
    | Reflect t1 ->
        let uu____3810 = t_to_string t1  in
        FStar_String.op_Hat "Reflect " uu____3810
    | Quote uu____3813 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____3820) ->
        let uu____3837 =
          let uu____3839 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____3839  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3837
    | Lazy (FStar_Util.Inr (uu____3841,et),uu____3843) ->
        let uu____3860 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3860
    | LocalLetRec
        (uu____3863,l,uu____3865,uu____3866,uu____3867,uu____3868,uu____3869)
        ->
        let uu____3900 =
          let uu____3902 = FStar_Syntax_Print.lbs_to_string [] (true, [l])
             in
          FStar_String.op_Hat uu____3902 ")"  in
        FStar_String.op_Hat "LocalLetRec (" uu____3900
    | TopLevelLet (lb,uu____3911,uu____3912) ->
        let uu____3927 =
          let uu____3929 =
            let uu____3931 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3931  in
          FStar_String.op_Hat uu____3929 ")"  in
        FStar_String.op_Hat "TopLevelLet (" uu____3927
    | TopLevelRec (lb,uu____3935,uu____3936,uu____3937) ->
        let uu____3958 =
          let uu____3960 =
            let uu____3962 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3962  in
          FStar_String.op_Hat uu____3960 ")"  in
        FStar_String.op_Hat "TopLevelRec (" uu____3958

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v ->
        let uu____3968 = FStar_Syntax_Print.bv_to_string v  in
        FStar_String.op_Hat "Var " uu____3968
    | Match (t1,uu____3972) ->
        let uu____3983 = t_to_string t1  in
        FStar_String.op_Hat "Match " uu____3983
    | UnreducedLet (var1,typ,def,body,lb) ->
        let uu____4003 =
          let uu____4005 = FStar_Syntax_Print.lbs_to_string [] (false, [lb])
             in
          FStar_String.op_Hat uu____4005 " in ...)"  in
        FStar_String.op_Hat "UnreducedLet(" uu____4003
    | UnreducedLetRec (uu____4013,body,lbs) ->
        let uu____4036 =
          let uu____4038 = FStar_Syntax_Print.lbs_to_string [] (true, lbs)
             in
          let uu____4044 =
            let uu____4046 =
              let uu____4048 = t_to_string body  in
              FStar_String.op_Hat uu____4048 ")"  in
            FStar_String.op_Hat " in " uu____4046  in
          FStar_String.op_Hat uu____4038 uu____4044  in
        FStar_String.op_Hat "UnreducedLetRec(" uu____4036
    | UVar uu____4053 -> "UVar"

let (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____4064 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____4064 t_to_string
  
let (args_to_string : args -> Prims.string) =
  fun args1  ->
    let uu____4077 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____4077 (FStar_String.concat " ")
  
type nbe_cbs =
  {
  iapp: t -> args -> t ;
  translate: FStar_Syntax_Syntax.term -> t }
let (__proj__Mknbe_cbs__item__iapp : nbe_cbs -> t -> args -> t) =
  fun projectee  -> match projectee with | { iapp; translate;_} -> iapp 
let (__proj__Mknbe_cbs__item__translate :
  nbe_cbs -> FStar_Syntax_Syntax.term -> t) =
  fun projectee  -> match projectee with | { iapp; translate;_} -> translate 
let (iapp_cb : nbe_cbs -> t -> args -> t) =
  fun cbs  -> fun h  -> fun a  -> cbs.iapp h a 
let (translate_cb : nbe_cbs -> FStar_Syntax_Syntax.term -> t) =
  fun cbs  -> fun t1  -> cbs.translate t1 
type 'a embedding =
  {
  em: nbe_cbs -> 'a -> t ;
  un: nbe_cbs -> t -> 'a FStar_Pervasives_Native.option ;
  typ: t ;
  emb_typ: FStar_Syntax_Syntax.emb_typ }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> nbe_cbs -> 'a -> t =
  fun projectee  -> match projectee with | { em; un; typ; emb_typ;_} -> em 
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> nbe_cbs -> t -> 'a FStar_Pervasives_Native.option =
  fun projectee  -> match projectee with | { em; un; typ; emb_typ;_} -> un 
let __proj__Mkembedding__item__typ : 'a . 'a embedding -> t =
  fun projectee  -> match projectee with | { em; un; typ; emb_typ;_} -> typ 
let __proj__Mkembedding__item__emb_typ :
  'a . 'a embedding -> FStar_Syntax_Syntax.emb_typ =
  fun projectee  ->
    match projectee with | { em; un; typ; emb_typ;_} -> emb_typ
  
let embed : 'a . 'a embedding -> nbe_cbs -> 'a -> t =
  fun e  -> fun cb  -> fun x  -> e.em cb x 
let unembed :
  'a . 'a embedding -> nbe_cbs -> t -> 'a FStar_Pervasives_Native.option =
  fun e  -> fun cb  -> fun trm  -> e.un cb trm 
let type_of : 'a . 'a embedding -> t = fun e  -> e.typ 
let mk_emb :
  'a .
    (nbe_cbs -> 'a -> t) ->
      (nbe_cbs -> t -> 'a FStar_Pervasives_Native.option) ->
        t -> FStar_Syntax_Syntax.emb_typ -> 'a embedding
  =
  fun em  -> fun un  -> fun typ  -> fun et  -> { em; un; typ; emb_typ = et } 
let mk_emb' :
  'uuuuuu4537 .
    (nbe_cbs -> 'uuuuuu4537 -> t') ->
      (nbe_cbs -> t' -> 'uuuuuu4537 FStar_Pervasives_Native.option) ->
        t -> FStar_Syntax_Syntax.emb_typ -> 'uuuuuu4537 embedding
  =
  fun em  ->
    fun un  ->
      mk_emb
        (fun cbs  ->
           fun t1  ->
             let uu____4587 = em cbs t1  in
             FStar_All.pipe_left mk_t uu____4587)
        (fun cbs  -> fun t1  -> un cbs t1.nbe_t)
  
let embed_as :
  'a 'b .
    'a embedding ->
      ('a -> 'b) ->
        ('b -> 'a) -> t FStar_Pervasives_Native.option -> 'b embedding
  =
  fun ea  ->
    fun ab  ->
      fun ba  ->
        fun ot  ->
          mk_emb
            (fun cbs  ->
               fun x  -> let uu____4652 = ba x  in embed ea cbs uu____4652)
            (fun cbs  ->
               fun t1  ->
                 let uu____4658 = unembed ea cbs t1  in
                 FStar_Util.map_opt uu____4658 ab)
            (match ot with
             | FStar_Pervasives_Native.Some t1 -> t1
             | FStar_Pervasives_Native.None  -> ea.typ) ea.emb_typ
  
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args1  ->
        let uu____4683 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____4683 us args1
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args1  ->
        let uu____4704 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____4704 us args1
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      FStar_All.pipe_left mk_t
        (Arrow
           (FStar_Util.Inr ([a], (Tot (t1, FStar_Pervasives_Native.None)))))
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____4787 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____4787
         then
           let uu____4811 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____4811
         else ());
        (let uu____4816 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____4816
         then f ()
         else
           (let thunk = FStar_Thunk.mk f  in
            let li = let uu____4850 = FStar_Dyn.mkdyn x  in (uu____4850, et)
               in
            FStar_All.pipe_left mk_t (Lazy ((FStar_Util.Inr li), thunk))))
  
let lazy_unembed :
  'uuuuuu4878 'a .
    'uuuuuu4878 ->
      FStar_Syntax_Syntax.emb_typ ->
        t ->
          (t -> 'a FStar_Pervasives_Native.option) ->
            'a FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun et  ->
      fun x  ->
        fun f  ->
          match x.nbe_t with
          | Lazy (FStar_Util.Inl li,thunk) ->
              let uu____4929 = FStar_Thunk.force thunk  in f uu____4929
          | Lazy (FStar_Util.Inr (b,et'),thunk) ->
              let uu____4949 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____4949
              then
                let res =
                  let uu____4978 = FStar_Thunk.force thunk  in f uu____4978
                   in
                ((let uu____4980 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4980
                  then
                    let uu____5004 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____5006 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____5004
                      uu____5006
                  else ());
                 res)
              else
                (let a1 = FStar_Dyn.undyn b  in
                 (let uu____5015 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____5015
                  then
                    let uu____5039 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____5039
                  else ());
                 FStar_Pervasives_Native.Some a1)
          | uu____5044 ->
              let aopt = f x  in
              ((let uu____5049 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____5049
                then
                  let uu____5073 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____5073
                else ());
               aopt)
  
let (mk_any_emb : t -> t embedding) =
  fun ty  ->
    let em _cb a = a  in
    let un _cb t1 = FStar_Pervasives_Native.Some t1  in
    mk_emb em un ty FStar_Syntax_Syntax.ET_abstract
  
let (e_any : t embedding) =
  let em _cb a = a  in
  let un _cb t1 = FStar_Pervasives_Native.Some t1  in
  let uu____5141 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____5141 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t1 = FStar_Pervasives_Native.Some ()  in
  let uu____5175 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____5180 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb' em un uu____5175 uu____5180 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t1 =
    match t1 with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____5221 -> FStar_Pervasives_Native.None  in
  let uu____5223 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____5228 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb' em un uu____5223 uu____5228 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____5270 -> FStar_Pervasives_Native.None  in
  let uu____5272 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____5277 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb' em un uu____5272 uu____5277 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____5319)) -> FStar_Pervasives_Native.Some s1
    | uu____5323 -> FStar_Pervasives_Native.None  in
  let uu____5325 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____5330 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb' em un uu____5325 uu____5330 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____5365 -> FStar_Pervasives_Native.None  in
  let uu____5366 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____5371 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb' em un uu____5366 uu____5371 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____5392 =
        let uu____5400 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____5400, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5392  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____5425  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____5426 =
                 let uu____5427 =
                   let uu____5432 = type_of ea  in as_iarg uu____5432  in
                 [uu____5427]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____5426
           | FStar_Pervasives_Native.Some x ->
               let uu____5442 =
                 let uu____5443 =
                   let uu____5448 = embed ea cb x  in as_arg uu____5448  in
                 let uu____5449 =
                   let uu____5456 =
                     let uu____5461 = type_of ea  in as_iarg uu____5461  in
                   [uu____5456]  in
                 uu____5443 :: uu____5449  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____5442)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1.nbe_t with
           | Construct (fvar,us,args1) when
               FStar_Syntax_Syntax.fv_eq_lid fvar FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar,us,(a1,uu____5528)::uu____5529::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar FStar_Parser_Const.some_lid
               ->
               let uu____5556 = unembed ea cb a1  in
               FStar_Util.bind_opt uu____5556
                 (fun a2  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a2))
           | uu____5565 -> FStar_Pervasives_Native.None)
       in
    let uu____5568 =
      let uu____5569 =
        let uu____5570 = let uu____5575 = type_of ea  in as_arg uu____5575
           in
        [uu____5570]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____5569
       in
    mk_emb em un uu____5568 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5622 =
          let uu____5630 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____5630, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5622  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____5661  ->
             let uu____5662 =
               let uu____5663 =
                 let uu____5668 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____5668  in
               let uu____5669 =
                 let uu____5676 =
                   let uu____5681 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____5681  in
                 let uu____5682 =
                   let uu____5689 =
                     let uu____5694 = type_of eb  in as_iarg uu____5694  in
                   let uu____5695 =
                     let uu____5702 =
                       let uu____5707 = type_of ea  in as_iarg uu____5707  in
                     [uu____5702]  in
                   uu____5689 :: uu____5695  in
                 uu____5676 :: uu____5682  in
               uu____5663 :: uu____5669  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____5662)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1.nbe_t with
             | Construct
                 (fvar,us,(b1,uu____5775)::(a1,uu____5777)::uu____5778::uu____5779::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____5818 = unembed ea cb a1  in
                 FStar_Util.bind_opt uu____5818
                   (fun a2  ->
                      let uu____5828 = unembed eb cb b1  in
                      FStar_Util.bind_opt uu____5828
                        (fun b2  -> FStar_Pervasives_Native.Some (a2, b2)))
             | uu____5841 -> FStar_Pervasives_Native.None)
         in
      let uu____5846 =
        let uu____5847 =
          let uu____5848 = let uu____5853 = type_of eb  in as_arg uu____5853
             in
          let uu____5854 =
            let uu____5861 =
              let uu____5866 = type_of ea  in as_arg uu____5866  in
            [uu____5861]  in
          uu____5848 :: uu____5854  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5847
         in
      mk_emb em un uu____5846 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5919 =
          let uu____5927 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____5927, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5919  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____5959  ->
             match s with
             | FStar_Util.Inl a1 ->
                 let uu____5961 =
                   let uu____5962 =
                     let uu____5967 = embed ea cb a1  in as_arg uu____5967
                      in
                   let uu____5968 =
                     let uu____5975 =
                       let uu____5980 = type_of eb  in as_iarg uu____5980  in
                     let uu____5981 =
                       let uu____5988 =
                         let uu____5993 = type_of ea  in as_iarg uu____5993
                          in
                       [uu____5988]  in
                     uu____5975 :: uu____5981  in
                   uu____5962 :: uu____5968  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5961
             | FStar_Util.Inr b1 ->
                 let uu____6011 =
                   let uu____6012 =
                     let uu____6017 = embed eb cb b1  in as_arg uu____6017
                      in
                   let uu____6018 =
                     let uu____6025 =
                       let uu____6030 = type_of eb  in as_iarg uu____6030  in
                     let uu____6031 =
                       let uu____6038 =
                         let uu____6043 = type_of ea  in as_iarg uu____6043
                          in
                       [uu____6038]  in
                     uu____6025 :: uu____6031  in
                   uu____6012 :: uu____6018  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____6011)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1.nbe_t with
             | Construct
                 (fvar,us,(a1,uu____6105)::uu____6106::uu____6107::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____6142 = unembed ea cb a1  in
                 FStar_Util.bind_opt uu____6142
                   (fun a2  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a2))
             | Construct
                 (fvar,us,(b1,uu____6158)::uu____6159::uu____6160::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____6195 = unembed eb cb b1  in
                 FStar_Util.bind_opt uu____6195
                   (fun b2  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b2))
             | uu____6208 -> FStar_Pervasives_Native.None)
         in
      let uu____6213 =
        let uu____6214 =
          let uu____6215 = let uu____6220 = type_of eb  in as_arg uu____6220
             in
          let uu____6221 =
            let uu____6228 =
              let uu____6233 = type_of ea  in as_arg uu____6233  in
            [uu____6228]  in
          uu____6215 :: uu____6221  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____6214
         in
      mk_emb em un uu____6213 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t1 =
    match t1 with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____6282 -> FStar_Pervasives_Native.None  in
  let uu____6283 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____6288 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb' em un uu____6283 uu____6288 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____6309 =
        let uu____6317 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____6317, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____6309  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____6344  ->
           let typ = let uu____6346 = type_of ea  in as_iarg uu____6346  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons hd tl =
             let uu____6367 =
               let uu____6368 = as_arg tl  in
               let uu____6373 =
                 let uu____6380 =
                   let uu____6385 = embed ea cb hd  in as_arg uu____6385  in
                 [uu____6380; typ]  in
               uu____6368 :: uu____6373  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____6367
              in
           FStar_List.fold_right cons l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1.nbe_t with
           | Construct (fv,uu____6433,uu____6434) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____6454,(tl,FStar_Pervasives_Native.None )::(hd,FStar_Pervasives_Native.None
                                                                   )::
                (uu____6457,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6458))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____6486 = unembed ea cb hd  in
               FStar_Util.bind_opt uu____6486
                 (fun hd1  ->
                    let uu____6494 = un cb tl  in
                    FStar_Util.bind_opt uu____6494
                      (fun tl1  -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | Construct
               (fv,uu____6510,(tl,FStar_Pervasives_Native.None )::(hd,FStar_Pervasives_Native.None
                                                                   )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____6535 = unembed ea cb hd  in
               FStar_Util.bind_opt uu____6535
                 (fun hd1  ->
                    let uu____6543 = un cb tl  in
                    FStar_Util.bind_opt uu____6543
                      (fun tl1  -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | uu____6558 -> FStar_Pervasives_Native.None)
       in
    let uu____6561 =
      let uu____6562 =
        let uu____6563 = let uu____6568 = type_of ea  in as_arg uu____6568
           in
        [uu____6563]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____6562
       in
    mk_emb em un uu____6561 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____6642  ->
             let uu____6643 =
               let uu____6644 =
                 let uu____6677 =
                   let uu____6698 =
                     let uu____6705 =
                       let uu____6710 = type_of eb  in as_arg uu____6710  in
                     [uu____6705]  in
                   FStar_Util.Inr uu____6698  in
                 ((fun tas  ->
                     let uu____6768 =
                       let uu____6771 = FStar_List.hd tas  in
                       unembed ea cb uu____6771  in
                     match uu____6768 with
                     | FStar_Pervasives_Native.Some a1 ->
                         let uu____6773 = f a1  in embed eb cb uu____6773
                     | FStar_Pervasives_Native.None  ->
                         failwith "cannot unembed function argument"),
                   uu____6677, Prims.int_one)
                  in
               Lam uu____6644  in
             FStar_All.pipe_left mk_t uu____6643)
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____6820 =
                 let uu____6823 =
                   let uu____6824 =
                     let uu____6825 =
                       let uu____6830 = embed ea cb x  in as_arg uu____6830
                        in
                     [uu____6825]  in
                   cb.iapp lam1 uu____6824  in
                 unembed eb cb uu____6823  in
               match uu____6820 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____6844 =
        let uu____6845 = type_of ea  in
        let uu____6846 = let uu____6847 = type_of eb  in as_iarg uu____6847
           in
        make_arrow1 uu____6845 uu____6846  in
      mk_emb em un uu____6844 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n =
    match n with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____6865 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6865 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____6870 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6870 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____6875 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6875 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____6880 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6880 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____6885 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6885 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____6890 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6890 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____6895 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6895 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____6900 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6900 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____6905 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6905 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____6914 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6915 =
          let uu____6916 =
            let uu____6921 =
              let uu____6922 = e_list e_string  in embed uu____6922 cb l  in
            as_arg uu____6921  in
          [uu____6916]  in
        mkFV uu____6914 [] uu____6915
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____6944 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6945 =
          let uu____6946 =
            let uu____6951 =
              let uu____6952 = e_list e_string  in embed uu____6952 cb l  in
            as_arg uu____6951  in
          [uu____6946]  in
        mkFV uu____6944 [] uu____6945
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____6974 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6975 =
          let uu____6976 =
            let uu____6981 =
              let uu____6982 = e_list e_string  in embed uu____6982 cb l  in
            as_arg uu____6981  in
          [uu____6976]  in
        mkFV uu____6974 [] uu____6975
     in
  let un cb t0 =
    match t0.nbe_t with
    | FV (fv,uu____7016,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____7032,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____7048,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____7064,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____7080,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____7096,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____7112,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____7128,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____7144,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____7160,(l,uu____7162)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____7181 =
          let uu____7187 = e_list e_string  in unembed uu____7187 cb l  in
        FStar_Util.bind_opt uu____7181
          (fun ss  ->
             FStar_All.pipe_left
               (fun uu____7207  -> FStar_Pervasives_Native.Some uu____7207)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____7209,(l,uu____7211)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____7230 =
          let uu____7236 = e_list e_string  in unembed uu____7236 cb l  in
        FStar_Util.bind_opt uu____7230
          (fun ss  ->
             FStar_All.pipe_left
               (fun uu____7256  -> FStar_Pervasives_Native.Some uu____7256)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____7258,(l,uu____7260)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____7279 =
          let uu____7285 = e_list e_string  in unembed uu____7285 cb l  in
        FStar_Util.bind_opt uu____7279
          (fun ss  ->
             FStar_All.pipe_left
               (fun uu____7305  -> FStar_Pervasives_Native.Some uu____7305)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____7306 ->
        ((let uu____7308 =
            let uu____7314 =
              let uu____7316 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____7316
               in
            (FStar_Errors.Warning_NotEmbedded, uu____7314)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____7308);
         FStar_Pervasives_Native.None)
     in
  let uu____7320 =
    let uu____7321 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____7321 [] []  in
  let uu____7326 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____7320 uu____7326 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____7335  -> failwith "bogus_cbs translate")
  } 
let (arg_as_int : arg -> FStar_BigInt.t FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_int bogus_cbs)
  
let (arg_as_bool : arg -> Prims.bool FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_bool bogus_cbs)
  
let (arg_as_char : arg -> FStar_Char.char FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_char bogus_cbs)
  
let (arg_as_string : arg -> Prims.string FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_string bogus_cbs)
  
let arg_as_list :
  'a . 'a embedding -> arg -> 'a Prims.list FStar_Pervasives_Native.option =
  fun e  ->
    fun a1  ->
      let uu____7412 =
        let uu____7421 = e_list e  in unembed uu____7421 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a1) uu____7412
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____7443  ->
    match uu____7443 with
    | (a,uu____7451) ->
        (match a.nbe_t with
         | FV
             (fv1,[],({ nbe_t = Constant (Int i); nbe_r = uu____7466;_},uu____7467)::[])
             when
             let uu____7484 =
               FStar_Ident.string_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____7484 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____7491 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t  ->
    fun n  ->
      let c = embed e_int bogus_cbs n  in
      let int_to_t1 args1 =
        FStar_All.pipe_left mk_t (FV (int_to_t, [], args1))  in
      let uu____7534 = let uu____7541 = as_arg c  in [uu____7541]  in
      int_to_t1 uu____7534
  
let lift_unary :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun aopts  ->
      match aopts with
      | (FStar_Pervasives_Native.Some a1)::[] ->
          let uu____7595 = f a1  in FStar_Pervasives_Native.Some uu____7595
      | uu____7596 -> FStar_Pervasives_Native.None
  
let lift_binary :
  'a 'b .
    ('a -> 'a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun aopts  ->
      match aopts with
      | (FStar_Pervasives_Native.Some a0)::(FStar_Pervasives_Native.Some
          a1)::[] ->
          let uu____7650 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____7650
      | uu____7651 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args1  ->
        let uu____7695 = FStar_List.map as_a args1  in
        lift_unary f uu____7695
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args1  ->
        let uu____7750 = FStar_List.map as_a args1  in
        lift_binary f uu____7750
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____7780 = f x  in embed e_int bogus_cbs uu____7780)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____7807 = f x y  in embed e_int bogus_cbs uu____7807)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____7833 = f x  in embed e_bool bogus_cbs uu____7833)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____7871 = f x y  in embed e_bool bogus_cbs uu____7871)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____7909 = f x y  in embed e_string bogus_cbs uu____7909)
  
let mixed_binary_op :
  'a 'b 'c .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      (arg -> 'b FStar_Pervasives_Native.option) ->
        ('c -> t) ->
          ('a -> 'b -> 'c) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun as_b  ->
      fun embed_c  ->
        fun f  ->
          fun args1  ->
            match args1 with
            | a1::b1::[] ->
                let uu____8014 =
                  let uu____8023 = as_a a1  in
                  let uu____8026 = as_b b1  in (uu____8023, uu____8026)  in
                (match uu____8014 with
                 | (FStar_Pervasives_Native.Some
                    a2,FStar_Pervasives_Native.Some b2) ->
                     let uu____8041 =
                       let uu____8042 = f a2 b2  in embed_c uu____8042  in
                     FStar_Pervasives_Native.Some uu____8041
                 | uu____8043 -> FStar_Pervasives_Native.None)
            | uu____8052 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____8061 = e_list e_char  in
    let uu____8068 = FStar_String.list_of_string s  in
    embed uu____8061 bogus_cbs uu____8068
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    FStar_All.pipe_left mk_t (Constant (String (s, FStar_Range.dummyRange)))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____8107 =
        let uu____8108 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____8108  in
      embed e_int bogus_cbs uu____8107
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8142 = arg_as_string a1  in
        (match uu____8142 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8151 = arg_as_list e_string a2  in
             (match uu____8151 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____8169 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____8169
              | uu____8171 -> FStar_Pervasives_Native.None)
         | uu____8177 -> FStar_Pervasives_Native.None)
    | uu____8181 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____8188 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____8188
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string bogus_cbs (if b then "true" else "false") 
let (string_lowercase : Prims.string -> t) =
  fun s  -> embed e_string bogus_cbs (FStar_String.lowercase s) 
let (string_uppercase : Prims.string -> t) =
  fun s  -> embed e_string bogus_cbs (FStar_String.lowercase s) 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args1  ->
      let tru = embed e_bool bogus_cbs true  in
      let fal = embed e_bool bogus_cbs false  in
      match args1 with
      | (_typ,uu____8250)::(a1,uu____8252)::(a2,uu____8254)::[] ->
          let uu____8271 = eq_t a1 a2  in
          (match uu____8271 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____8280 -> FStar_Pervasives_Native.None)
      | uu____8281 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | (_u,uu____8296)::(_typ,uu____8298)::(a1,uu____8300)::(a2,uu____8302)::[]
        ->
        let uu____8323 = eq_t a1 a2  in
        (match uu____8323 with
         | FStar_Syntax_Util.Equal  ->
             let uu____8326 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____8326
         | FStar_Syntax_Util.NotEqual  ->
             let uu____8329 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____8329
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____8332 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | (_u,uu____8347)::(_v,uu____8349)::(t1,uu____8351)::(t2,uu____8353)::
        (a1,uu____8355)::(a2,uu____8357)::[] ->
        let uu____8386 =
          let uu____8387 = eq_t t1 t2  in
          let uu____8388 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____8387 uu____8388  in
        (match uu____8386 with
         | FStar_Syntax_Util.Equal  ->
             let uu____8391 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____8391
         | FStar_Syntax_Util.NotEqual  ->
             let uu____8394 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____8394
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____8397 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args1  ->
      let uu____8416 =
        let uu____8418 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____8418  in
      failwith uu____8416
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | (a1,uu____8434)::[] ->
        let uu____8443 = unembed e_range bogus_cbs a1  in
        (match uu____8443 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8449 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8449
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8450 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8486 = arg_as_list e_char a1  in
        (match uu____8486 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8502 = arg_as_string a2  in
             (match uu____8502 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____8515 =
                    let uu____8516 = e_list e_string  in
                    embed uu____8516 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____8515
              | uu____8526 -> FStar_Pervasives_Native.None)
         | uu____8530 -> FStar_Pervasives_Native.None)
    | uu____8536 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8569 =
          let uu____8579 = arg_as_string a1  in
          let uu____8583 = arg_as_int a2  in (uu____8579, uu____8583)  in
        (match uu____8569 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1042_8607  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____8612 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8612) ()
              with | uu___1041_8615 -> FStar_Pervasives_Native.None)
         | uu____8618 -> FStar_Pervasives_Native.None)
    | uu____8628 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8661 =
          let uu____8672 = arg_as_string a1  in
          let uu____8676 = arg_as_char a2  in (uu____8672, uu____8676)  in
        (match uu____8661 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1060_8705  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____8709 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8709) ()
              with | uu___1059_8711 -> FStar_Pervasives_Native.None)
         | uu____8714 -> FStar_Pervasives_Native.None)
    | uu____8725 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::a3::[] ->
        let uu____8767 =
          let uu____8781 = arg_as_string a1  in
          let uu____8785 = arg_as_int a2  in
          let uu____8788 = arg_as_int a3  in
          (uu____8781, uu____8785, uu____8788)  in
        (match uu____8767 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1083_8821  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____8826 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8826) ()
              with | uu___1082_8829 -> FStar_Pervasives_Native.None)
         | uu____8832 -> FStar_Pervasives_Native.None)
    | uu____8846 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8906 =
          let uu____8928 = arg_as_string fn  in
          let uu____8932 = arg_as_int from_line  in
          let uu____8935 = arg_as_int from_col  in
          let uu____8938 = arg_as_int to_line  in
          let uu____8941 = arg_as_int to_col  in
          (uu____8928, uu____8932, uu____8935, uu____8938, uu____8941)  in
        (match uu____8906 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8976 =
                 let uu____8977 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8979 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8977 uu____8979  in
               let uu____8981 =
                 let uu____8982 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8984 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8982 uu____8984  in
               FStar_Range.mk_range fn1 uu____8976 uu____8981  in
             let uu____8986 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8986
         | uu____8987 -> FStar_Pervasives_Native.None)
    | uu____9009 -> FStar_Pervasives_Native.None
  
let arrow_as_prim_step_1 :
  'a 'b .
    'a embedding ->
      'b embedding ->
        ('a -> 'b) ->
          Prims.int ->
            FStar_Ident.lid ->
              nbe_cbs -> args -> t FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun f  ->
        fun n_tvars  ->
          fun _fv_lid  ->
            fun cb  ->
              let f_wrapped args1 =
                let uu____9099 = FStar_List.splitAt n_tvars args1  in
                match uu____9099 with
                | (_tvar_args,rest_args) ->
                    let uu____9148 = FStar_List.hd rest_args  in
                    (match uu____9148 with
                     | (x,uu____9160) ->
                         let uu____9161 = unembed ea cb x  in
                         FStar_Util.map_opt uu____9161
                           (fun x1  ->
                              let uu____9167 = f x1  in
                              embed eb cb uu____9167))
                 in
              f_wrapped
  
let arrow_as_prim_step_2 :
  'a 'b 'c .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          ('a -> 'b -> 'c) ->
            Prims.int ->
              FStar_Ident.lid ->
                nbe_cbs -> args -> t FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun f  ->
          fun n_tvars  ->
            fun _fv_lid  ->
              fun cb  ->
                let f_wrapped args1 =
                  let uu____9276 = FStar_List.splitAt n_tvars args1  in
                  match uu____9276 with
                  | (_tvar_args,rest_args) ->
                      let uu____9325 = FStar_List.hd rest_args  in
                      (match uu____9325 with
                       | (x,uu____9337) ->
                           let uu____9338 =
                             let uu____9343 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____9343  in
                           (match uu____9338 with
                            | (y,uu____9361) ->
                                let uu____9362 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____9362
                                  (fun x1  ->
                                     let uu____9368 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____9368
                                       (fun y1  ->
                                          let uu____9374 =
                                            let uu____9375 = f x1 y1  in
                                            embed ec cb uu____9375  in
                                          FStar_Pervasives_Native.Some
                                            uu____9374))))
                   in
                f_wrapped
  
let arrow_as_prim_step_3 :
  'a 'b 'c 'd .
    'a embedding ->
      'b embedding ->
        'c embedding ->
          'd embedding ->
            ('a -> 'b -> 'c -> 'd) ->
              Prims.int ->
                FStar_Ident.lid ->
                  nbe_cbs -> args -> t FStar_Pervasives_Native.option
  =
  fun ea  ->
    fun eb  ->
      fun ec  ->
        fun ed  ->
          fun f  ->
            fun n_tvars  ->
              fun _fv_lid  ->
                fun cb  ->
                  let f_wrapped args1 =
                    let uu____9503 = FStar_List.splitAt n_tvars args1  in
                    match uu____9503 with
                    | (_tvar_args,rest_args) ->
                        let uu____9552 = FStar_List.hd rest_args  in
                        (match uu____9552 with
                         | (x,uu____9564) ->
                             let uu____9565 =
                               let uu____9570 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____9570  in
                             (match uu____9565 with
                              | (y,uu____9588) ->
                                  let uu____9589 =
                                    let uu____9594 =
                                      let uu____9601 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____9601  in
                                    FStar_List.hd uu____9594  in
                                  (match uu____9589 with
                                   | (z,uu____9623) ->
                                       let uu____9624 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____9624
                                         (fun x1  ->
                                            let uu____9630 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____9630
                                              (fun y1  ->
                                                 let uu____9636 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____9636
                                                   (fun z1  ->
                                                      let uu____9642 =
                                                        let uu____9643 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____9643
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____9642))))))
                     in
                  f_wrapped
  