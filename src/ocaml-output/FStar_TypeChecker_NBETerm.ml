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
  
let (mk_t : t' -> t) =
  fun t1  -> { nbe_t = t1; nbe_r = FStar_Range.dummyRange } 
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
  = fun i  -> fun us  -> fun ts  -> FStar_All.pipe_left mk_t (FV (i, us, ts)) 
let (mkAccuVar : var -> t) =
  fun v  -> FStar_All.pipe_left mk_t (Accu ((Var v), [])) 
let (mkAccuMatch : t -> (unit -> FStar_Syntax_Syntax.branch Prims.list) -> t)
  =
  fun s  -> fun bs  -> FStar_All.pipe_left mk_t (Accu ((Match (s, bs)), [])) 
let (equal_if : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___0_2852  ->
    if uu___0_2852
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2863  ->
    if uu___1_2863
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
      | (FStar_Syntax_Util.NotEqual ,uu____2879) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2880,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____2881) -> FStar_Syntax_Util.Unknown
      | (uu____2882,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____2899 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____2919),String (s2,uu____2921)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2934,uu____2935) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match ((t1.nbe_t), (t2.nbe_t)) with
      | (Lam uu____2971,Lam uu____2972) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____3065 = eq_atom a1 a2  in
          eq_and uu____3065 (fun uu____3067  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____3106 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____3106
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____3122 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____3179  ->
                        match uu____3179 with
                        | ((a1,uu____3193),(a2,uu____3195)) ->
                            let uu____3204 = eq_t a1 a2  in
                            eq_inj acc uu____3204) FStar_Syntax_Util.Equal)
                uu____3122))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____3245 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____3245
          then
            let uu____3248 =
              let uu____3249 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____3249  in
            eq_and uu____3248 (fun uu____3252  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____3259 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____3259
      | (Univ u1,Univ u2) ->
          let uu____3263 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____3263
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____3310 =
            let uu____3311 =
              let uu____3312 = t11 ()  in
              FStar_Pervasives_Native.fst uu____3312  in
            let uu____3317 =
              let uu____3318 = t21 ()  in
              FStar_Pervasives_Native.fst uu____3318  in
            eq_t uu____3311 uu____3317  in
          eq_and uu____3310
            (fun uu____3326  ->
               let uu____3327 =
                 let uu____3328 = mkAccuVar x  in r1 uu____3328  in
               let uu____3329 =
                 let uu____3330 = mkAccuVar x  in r2 uu____3330  in
               eq_t uu____3327 uu____3329)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____3331,uu____3332) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) ->
          let uu____3337 = FStar_Syntax_Syntax.bv_eq bv1 bv2  in
          equal_if uu____3337
      | (uu____3339,uu____3340) -> FStar_Syntax_Util.Unknown

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
          let uu____3421 = eq_arg x y  in
          eq_and uu____3421 (fun uu____3423  -> eq_args xs ys)
      | (uu____3424,uu____3425) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____3472) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____3477 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____3477
    | SConst s -> FStar_Syntax_Print.const_to_string s
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x.nbe_t with
    | Lam (b,uu____3495,arity) ->
        let uu____3549 = FStar_Util.string_of_int arity  in
        FStar_Util.format1 "Lam (_, %s args)" uu____3549
    | Accu (a,l) ->
        let uu____3566 =
          let uu____3568 = atom_to_string a  in
          let uu____3570 =
            let uu____3572 =
              let uu____3574 =
                let uu____3576 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____3576  in
              FStar_String.op_Hat uu____3574 ")"  in
            FStar_String.op_Hat ") (" uu____3572  in
          FStar_String.op_Hat uu____3568 uu____3570  in
        FStar_String.op_Hat "Accu (" uu____3566
    | Construct (fv,us,l) ->
        let uu____3614 =
          let uu____3616 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3618 =
            let uu____3620 =
              let uu____3622 =
                let uu____3624 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3624  in
              let uu____3630 =
                let uu____3632 =
                  let uu____3634 =
                    let uu____3636 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3636  in
                  FStar_String.op_Hat uu____3634 "]"  in
                FStar_String.op_Hat "] [" uu____3632  in
              FStar_String.op_Hat uu____3622 uu____3630  in
            FStar_String.op_Hat ") [" uu____3620  in
          FStar_String.op_Hat uu____3616 uu____3618  in
        FStar_String.op_Hat "Construct (" uu____3614
    | FV (fv,us,l) ->
        let uu____3675 =
          let uu____3677 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3679 =
            let uu____3681 =
              let uu____3683 =
                let uu____3685 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3685  in
              let uu____3691 =
                let uu____3693 =
                  let uu____3695 =
                    let uu____3697 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3697  in
                  FStar_String.op_Hat uu____3695 "]"  in
                FStar_String.op_Hat "] [" uu____3693  in
              FStar_String.op_Hat uu____3683 uu____3691  in
            FStar_String.op_Hat ") [" uu____3681  in
          FStar_String.op_Hat uu____3677 uu____3679  in
        FStar_String.op_Hat "FV (" uu____3675
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____3719 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____3719
    | Type_t u ->
        let uu____3723 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____3723
    | Arrow uu____3726 -> "Arrow"
    | Refinement (f,t1) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t2 =
          let uu____3768 = t1 ()  in FStar_Pervasives_Native.fst uu____3768
           in
        let uu____3773 =
          let uu____3775 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____3777 =
            let uu____3779 =
              let uu____3781 = t_to_string t2  in
              let uu____3783 =
                let uu____3785 =
                  let uu____3787 =
                    let uu____3789 =
                      let uu____3790 = mkAccuVar x1  in f uu____3790  in
                    t_to_string uu____3789  in
                  FStar_String.op_Hat uu____3787 "}"  in
                FStar_String.op_Hat "{" uu____3785  in
              FStar_String.op_Hat uu____3781 uu____3783  in
            FStar_String.op_Hat ":" uu____3779  in
          FStar_String.op_Hat uu____3775 uu____3777  in
        FStar_String.op_Hat "Refinement " uu____3773
    | Unknown  -> "Unknown"
    | Reflect t1 ->
        let uu____3797 = t_to_string t1  in
        FStar_String.op_Hat "Reflect " uu____3797
    | Quote uu____3800 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____3807) ->
        let uu____3824 =
          let uu____3826 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____3826  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3824
    | Lazy (FStar_Util.Inr (uu____3828,et),uu____3830) ->
        let uu____3847 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3847
    | LocalLetRec
        (uu____3850,l,uu____3852,uu____3853,uu____3854,uu____3855,uu____3856)
        ->
        let uu____3887 =
          let uu____3889 = FStar_Syntax_Print.lbs_to_string [] (true, [l])
             in
          FStar_String.op_Hat uu____3889 ")"  in
        FStar_String.op_Hat "LocalLetRec (" uu____3887
    | TopLevelLet (lb,uu____3898,uu____3899) ->
        let uu____3914 =
          let uu____3916 =
            let uu____3918 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3918  in
          FStar_String.op_Hat uu____3916 ")"  in
        FStar_String.op_Hat "TopLevelLet (" uu____3914
    | TopLevelRec (lb,uu____3922,uu____3923,uu____3924) ->
        let uu____3945 =
          let uu____3947 =
            let uu____3949 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3949  in
          FStar_String.op_Hat uu____3947 ")"  in
        FStar_String.op_Hat "TopLevelRec (" uu____3945

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v ->
        let uu____3955 = FStar_Syntax_Print.bv_to_string v  in
        FStar_String.op_Hat "Var " uu____3955
    | Match (t1,uu____3959) ->
        let uu____3970 = t_to_string t1  in
        FStar_String.op_Hat "Match " uu____3970
    | UnreducedLet (var1,typ,def,body,lb) ->
        let uu____3990 =
          let uu____3992 = FStar_Syntax_Print.lbs_to_string [] (false, [lb])
             in
          FStar_String.op_Hat uu____3992 " in ...)"  in
        FStar_String.op_Hat "UnreducedLet(" uu____3990
    | UnreducedLetRec (uu____4000,body,lbs) ->
        let uu____4023 =
          let uu____4025 = FStar_Syntax_Print.lbs_to_string [] (true, lbs)
             in
          let uu____4031 =
            let uu____4033 =
              let uu____4035 = t_to_string body  in
              FStar_String.op_Hat uu____4035 ")"  in
            FStar_String.op_Hat " in " uu____4033  in
          FStar_String.op_Hat uu____4025 uu____4031  in
        FStar_String.op_Hat "UnreducedLetRec(" uu____4023
    | UVar uu____4040 -> "UVar"

let (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____4051 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____4051 t_to_string
  
let (args_to_string : args -> Prims.string) =
  fun args1  ->
    let uu____4064 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____4064 (FStar_String.concat " ")
  
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
  'uuuuuu4524 .
    (nbe_cbs -> 'uuuuuu4524 -> t') ->
      (nbe_cbs -> t' -> 'uuuuuu4524 FStar_Pervasives_Native.option) ->
        t -> FStar_Syntax_Syntax.emb_typ -> 'uuuuuu4524 embedding
  =
  fun em  ->
    fun un  ->
      mk_emb
        (fun cbs  ->
           fun t1  ->
             let uu____4574 = em cbs t1  in
             FStar_All.pipe_left mk_t uu____4574)
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
               fun x  -> let uu____4639 = ba x  in embed ea cbs uu____4639)
            (fun cbs  ->
               fun t1  ->
                 let uu____4645 = unembed ea cbs t1  in
                 FStar_Util.map_opt uu____4645 ab)
            (match ot with
             | FStar_Pervasives_Native.Some t1 -> t1
             | FStar_Pervasives_Native.None  -> ea.typ) ea.emb_typ
  
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args1  ->
        let uu____4670 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____4670 us args1
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args1  ->
        let uu____4691 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____4691 us args1
  
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
        (let uu____4774 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____4774
         then
           let uu____4798 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____4798
         else ());
        (let uu____4803 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____4803
         then f ()
         else
           (let thunk = FStar_Thunk.mk f  in
            let li = let uu____4837 = FStar_Dyn.mkdyn x  in (uu____4837, et)
               in
            FStar_All.pipe_left mk_t (Lazy ((FStar_Util.Inr li), thunk))))
  
let lazy_unembed :
  'uuuuuu4865 'a .
    'uuuuuu4865 ->
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
              let uu____4916 = FStar_Thunk.force thunk  in f uu____4916
          | Lazy (FStar_Util.Inr (b,et'),thunk) ->
              let uu____4936 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____4936
              then
                let res =
                  let uu____4965 = FStar_Thunk.force thunk  in f uu____4965
                   in
                ((let uu____4967 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4967
                  then
                    let uu____4991 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____4993 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____4991
                      uu____4993
                  else ());
                 res)
              else
                (let a1 = FStar_Dyn.undyn b  in
                 (let uu____5002 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____5002
                  then
                    let uu____5026 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____5026
                  else ());
                 FStar_Pervasives_Native.Some a1)
          | uu____5031 ->
              let aopt = f x  in
              ((let uu____5036 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____5036
                then
                  let uu____5060 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____5060
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
  let uu____5128 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____5128 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t1 = FStar_Pervasives_Native.Some ()  in
  let uu____5162 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____5167 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb' em un uu____5162 uu____5167 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t1 =
    match t1 with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____5208 -> FStar_Pervasives_Native.None  in
  let uu____5210 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____5215 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb' em un uu____5210 uu____5215 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____5257 -> FStar_Pervasives_Native.None  in
  let uu____5259 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____5264 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb' em un uu____5259 uu____5264 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____5306)) -> FStar_Pervasives_Native.Some s1
    | uu____5310 -> FStar_Pervasives_Native.None  in
  let uu____5312 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____5317 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb' em un uu____5312 uu____5317 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____5352 -> FStar_Pervasives_Native.None  in
  let uu____5353 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____5358 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb' em un uu____5353 uu____5358 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____5379 =
        let uu____5387 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____5387, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5379  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____5412  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____5413 =
                 let uu____5414 =
                   let uu____5419 = type_of ea  in as_iarg uu____5419  in
                 [uu____5414]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____5413
           | FStar_Pervasives_Native.Some x ->
               let uu____5429 =
                 let uu____5430 =
                   let uu____5435 = embed ea cb x  in as_arg uu____5435  in
                 let uu____5436 =
                   let uu____5443 =
                     let uu____5448 = type_of ea  in as_iarg uu____5448  in
                   [uu____5443]  in
                 uu____5430 :: uu____5436  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____5429)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1.nbe_t with
           | Construct (fvar,us,args1) when
               FStar_Syntax_Syntax.fv_eq_lid fvar FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar,us,(a1,uu____5515)::uu____5516::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar FStar_Parser_Const.some_lid
               ->
               let uu____5543 = unembed ea cb a1  in
               FStar_Util.bind_opt uu____5543
                 (fun a2  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a2))
           | uu____5552 -> FStar_Pervasives_Native.None)
       in
    let uu____5555 =
      let uu____5556 =
        let uu____5557 = let uu____5562 = type_of ea  in as_arg uu____5562
           in
        [uu____5557]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____5556
       in
    mk_emb em un uu____5555 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5609 =
          let uu____5617 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____5617, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5609  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____5648  ->
             let uu____5649 =
               let uu____5650 =
                 let uu____5655 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____5655  in
               let uu____5656 =
                 let uu____5663 =
                   let uu____5668 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____5668  in
                 let uu____5669 =
                   let uu____5676 =
                     let uu____5681 = type_of eb  in as_iarg uu____5681  in
                   let uu____5682 =
                     let uu____5689 =
                       let uu____5694 = type_of ea  in as_iarg uu____5694  in
                     [uu____5689]  in
                   uu____5676 :: uu____5682  in
                 uu____5663 :: uu____5669  in
               uu____5650 :: uu____5656  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____5649)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1.nbe_t with
             | Construct
                 (fvar,us,(b1,uu____5762)::(a1,uu____5764)::uu____5765::uu____5766::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____5805 = unembed ea cb a1  in
                 FStar_Util.bind_opt uu____5805
                   (fun a2  ->
                      let uu____5815 = unembed eb cb b1  in
                      FStar_Util.bind_opt uu____5815
                        (fun b2  -> FStar_Pervasives_Native.Some (a2, b2)))
             | uu____5828 -> FStar_Pervasives_Native.None)
         in
      let uu____5833 =
        let uu____5834 =
          let uu____5835 = let uu____5840 = type_of eb  in as_arg uu____5840
             in
          let uu____5841 =
            let uu____5848 =
              let uu____5853 = type_of ea  in as_arg uu____5853  in
            [uu____5848]  in
          uu____5835 :: uu____5841  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5834
         in
      mk_emb em un uu____5833 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5906 =
          let uu____5914 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____5914, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5906  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____5946  ->
             match s with
             | FStar_Util.Inl a1 ->
                 let uu____5948 =
                   let uu____5949 =
                     let uu____5954 = embed ea cb a1  in as_arg uu____5954
                      in
                   let uu____5955 =
                     let uu____5962 =
                       let uu____5967 = type_of eb  in as_iarg uu____5967  in
                     let uu____5968 =
                       let uu____5975 =
                         let uu____5980 = type_of ea  in as_iarg uu____5980
                          in
                       [uu____5975]  in
                     uu____5962 :: uu____5968  in
                   uu____5949 :: uu____5955  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5948
             | FStar_Util.Inr b1 ->
                 let uu____5998 =
                   let uu____5999 =
                     let uu____6004 = embed eb cb b1  in as_arg uu____6004
                      in
                   let uu____6005 =
                     let uu____6012 =
                       let uu____6017 = type_of eb  in as_iarg uu____6017  in
                     let uu____6018 =
                       let uu____6025 =
                         let uu____6030 = type_of ea  in as_iarg uu____6030
                          in
                       [uu____6025]  in
                     uu____6012 :: uu____6018  in
                   uu____5999 :: uu____6005  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5998)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1.nbe_t with
             | Construct
                 (fvar,us,(a1,uu____6092)::uu____6093::uu____6094::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____6129 = unembed ea cb a1  in
                 FStar_Util.bind_opt uu____6129
                   (fun a2  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a2))
             | Construct
                 (fvar,us,(b1,uu____6145)::uu____6146::uu____6147::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____6182 = unembed eb cb b1  in
                 FStar_Util.bind_opt uu____6182
                   (fun b2  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b2))
             | uu____6195 -> FStar_Pervasives_Native.None)
         in
      let uu____6200 =
        let uu____6201 =
          let uu____6202 = let uu____6207 = type_of eb  in as_arg uu____6207
             in
          let uu____6208 =
            let uu____6215 =
              let uu____6220 = type_of ea  in as_arg uu____6220  in
            [uu____6215]  in
          uu____6202 :: uu____6208  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____6201
         in
      mk_emb em un uu____6200 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t1 =
    match t1 with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____6269 -> FStar_Pervasives_Native.None  in
  let uu____6270 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____6275 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb' em un uu____6270 uu____6275 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____6296 =
        let uu____6304 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____6304, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____6296  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____6331  ->
           let typ = let uu____6333 = type_of ea  in as_iarg uu____6333  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons hd tl =
             let uu____6354 =
               let uu____6355 = as_arg tl  in
               let uu____6360 =
                 let uu____6367 =
                   let uu____6372 = embed ea cb hd  in as_arg uu____6372  in
                 [uu____6367; typ]  in
               uu____6355 :: uu____6360  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____6354
              in
           FStar_List.fold_right cons l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1.nbe_t with
           | Construct (fv,uu____6420,uu____6421) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____6441,(tl,FStar_Pervasives_Native.None )::(hd,FStar_Pervasives_Native.None
                                                                   )::
                (uu____6444,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6445))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____6473 = unembed ea cb hd  in
               FStar_Util.bind_opt uu____6473
                 (fun hd1  ->
                    let uu____6481 = un cb tl  in
                    FStar_Util.bind_opt uu____6481
                      (fun tl1  -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | Construct
               (fv,uu____6497,(tl,FStar_Pervasives_Native.None )::(hd,FStar_Pervasives_Native.None
                                                                   )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____6522 = unembed ea cb hd  in
               FStar_Util.bind_opt uu____6522
                 (fun hd1  ->
                    let uu____6530 = un cb tl  in
                    FStar_Util.bind_opt uu____6530
                      (fun tl1  -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | uu____6545 -> FStar_Pervasives_Native.None)
       in
    let uu____6548 =
      let uu____6549 =
        let uu____6550 = let uu____6555 = type_of ea  in as_arg uu____6555
           in
        [uu____6550]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____6549
       in
    mk_emb em un uu____6548 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____6629  ->
             let uu____6630 =
               let uu____6631 =
                 let uu____6664 =
                   let uu____6685 =
                     let uu____6692 =
                       let uu____6697 = type_of eb  in as_arg uu____6697  in
                     [uu____6692]  in
                   FStar_Util.Inr uu____6685  in
                 ((fun tas  ->
                     let uu____6755 =
                       let uu____6758 = FStar_List.hd tas  in
                       unembed ea cb uu____6758  in
                     match uu____6755 with
                     | FStar_Pervasives_Native.Some a1 ->
                         let uu____6760 = f a1  in embed eb cb uu____6760
                     | FStar_Pervasives_Native.None  ->
                         failwith "cannot unembed function argument"),
                   uu____6664, Prims.int_one)
                  in
               Lam uu____6631  in
             FStar_All.pipe_left mk_t uu____6630)
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____6807 =
                 let uu____6810 =
                   let uu____6811 =
                     let uu____6812 =
                       let uu____6817 = embed ea cb x  in as_arg uu____6817
                        in
                     [uu____6812]  in
                   cb.iapp lam1 uu____6811  in
                 unembed eb cb uu____6810  in
               match uu____6807 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____6831 =
        let uu____6832 = type_of ea  in
        let uu____6833 = let uu____6834 = type_of eb  in as_iarg uu____6834
           in
        make_arrow1 uu____6832 uu____6833  in
      mk_emb em un uu____6831 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n =
    match n with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____6852 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6852 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____6857 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6857 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____6862 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6862 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____6867 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6867 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____6872 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6872 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____6877 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6877 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____6882 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6882 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____6887 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6887 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____6892 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6892 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____6901 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6902 =
          let uu____6903 =
            let uu____6908 =
              let uu____6909 = e_list e_string  in embed uu____6909 cb l  in
            as_arg uu____6908  in
          [uu____6903]  in
        mkFV uu____6901 [] uu____6902
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____6931 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6932 =
          let uu____6933 =
            let uu____6938 =
              let uu____6939 = e_list e_string  in embed uu____6939 cb l  in
            as_arg uu____6938  in
          [uu____6933]  in
        mkFV uu____6931 [] uu____6932
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____6961 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6962 =
          let uu____6963 =
            let uu____6968 =
              let uu____6969 = e_list e_string  in embed uu____6969 cb l  in
            as_arg uu____6968  in
          [uu____6963]  in
        mkFV uu____6961 [] uu____6962
     in
  let un cb t0 =
    match t0.nbe_t with
    | FV (fv,uu____7003,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____7019,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____7035,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____7051,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____7067,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____7083,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____7099,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____7115,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____7131,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____7147,(l,uu____7149)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____7168 =
          let uu____7174 = e_list e_string  in unembed uu____7174 cb l  in
        FStar_Util.bind_opt uu____7168
          (fun ss  ->
             FStar_All.pipe_left
               (fun uu____7194  -> FStar_Pervasives_Native.Some uu____7194)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____7196,(l,uu____7198)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____7217 =
          let uu____7223 = e_list e_string  in unembed uu____7223 cb l  in
        FStar_Util.bind_opt uu____7217
          (fun ss  ->
             FStar_All.pipe_left
               (fun uu____7243  -> FStar_Pervasives_Native.Some uu____7243)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____7245,(l,uu____7247)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____7266 =
          let uu____7272 = e_list e_string  in unembed uu____7272 cb l  in
        FStar_Util.bind_opt uu____7266
          (fun ss  ->
             FStar_All.pipe_left
               (fun uu____7292  -> FStar_Pervasives_Native.Some uu____7292)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____7293 ->
        ((let uu____7295 =
            let uu____7301 =
              let uu____7303 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____7303
               in
            (FStar_Errors.Warning_NotEmbedded, uu____7301)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____7295);
         FStar_Pervasives_Native.None)
     in
  let uu____7307 =
    let uu____7308 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____7308 [] []  in
  let uu____7313 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____7307 uu____7313 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____7322  -> failwith "bogus_cbs translate")
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
      let uu____7399 =
        let uu____7408 = e_list e  in unembed uu____7408 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a1) uu____7399
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____7430  ->
    match uu____7430 with
    | (a,uu____7438) ->
        (match a.nbe_t with
         | FV
             (fv1,[],({ nbe_t = Constant (Int i); nbe_r = uu____7453;_},uu____7454)::[])
             when
             let uu____7471 =
               FStar_Ident.string_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____7471 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____7478 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t  ->
    fun n  ->
      let c = embed e_int bogus_cbs n  in
      let int_to_t1 args1 =
        FStar_All.pipe_left mk_t (FV (int_to_t, [], args1))  in
      let uu____7521 = let uu____7528 = as_arg c  in [uu____7528]  in
      int_to_t1 uu____7521
  
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
          let uu____7582 = f a1  in FStar_Pervasives_Native.Some uu____7582
      | uu____7583 -> FStar_Pervasives_Native.None
  
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
          let uu____7637 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____7637
      | uu____7638 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args1  ->
        let uu____7682 = FStar_List.map as_a args1  in
        lift_unary f uu____7682
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args1  ->
        let uu____7737 = FStar_List.map as_a args1  in
        lift_binary f uu____7737
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____7767 = f x  in embed e_int bogus_cbs uu____7767)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____7794 = f x y  in embed e_int bogus_cbs uu____7794)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____7820 = f x  in embed e_bool bogus_cbs uu____7820)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____7858 = f x y  in embed e_bool bogus_cbs uu____7858)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____7896 = f x y  in embed e_string bogus_cbs uu____7896)
  
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
                let uu____8001 =
                  let uu____8010 = as_a a1  in
                  let uu____8013 = as_b b1  in (uu____8010, uu____8013)  in
                (match uu____8001 with
                 | (FStar_Pervasives_Native.Some
                    a2,FStar_Pervasives_Native.Some b2) ->
                     let uu____8028 =
                       let uu____8029 = f a2 b2  in embed_c uu____8029  in
                     FStar_Pervasives_Native.Some uu____8028
                 | uu____8030 -> FStar_Pervasives_Native.None)
            | uu____8039 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____8048 = e_list e_char  in
    let uu____8055 = FStar_String.list_of_string s  in
    embed uu____8048 bogus_cbs uu____8055
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    FStar_All.pipe_left mk_t (Constant (String (s, FStar_Range.dummyRange)))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____8094 =
        let uu____8095 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____8095  in
      embed e_int bogus_cbs uu____8094
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8129 = arg_as_string a1  in
        (match uu____8129 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8138 = arg_as_list e_string a2  in
             (match uu____8138 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____8156 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____8156
              | uu____8158 -> FStar_Pervasives_Native.None)
         | uu____8164 -> FStar_Pervasives_Native.None)
    | uu____8168 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____8175 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____8175
  
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
      | (_typ,uu____8237)::(a1,uu____8239)::(a2,uu____8241)::[] ->
          let uu____8258 = eq_t a1 a2  in
          (match uu____8258 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____8267 -> FStar_Pervasives_Native.None)
      | uu____8268 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | (_u,uu____8283)::(_typ,uu____8285)::(a1,uu____8287)::(a2,uu____8289)::[]
        ->
        let uu____8310 = eq_t a1 a2  in
        (match uu____8310 with
         | FStar_Syntax_Util.Equal  ->
             let uu____8313 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____8313
         | FStar_Syntax_Util.NotEqual  ->
             let uu____8316 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____8316
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____8319 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | (_u,uu____8334)::(_v,uu____8336)::(t1,uu____8338)::(t2,uu____8340)::
        (a1,uu____8342)::(a2,uu____8344)::[] ->
        let uu____8373 =
          let uu____8374 = eq_t t1 t2  in
          let uu____8375 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____8374 uu____8375  in
        (match uu____8373 with
         | FStar_Syntax_Util.Equal  ->
             let uu____8378 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____8378
         | FStar_Syntax_Util.NotEqual  ->
             let uu____8381 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____8381
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____8384 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args1  ->
      let uu____8403 =
        let uu____8405 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____8405  in
      failwith uu____8403
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | (a1,uu____8421)::[] ->
        let uu____8430 = unembed e_range bogus_cbs a1  in
        (match uu____8430 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8436 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8436
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8437 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8473 = arg_as_list e_char a1  in
        (match uu____8473 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8489 = arg_as_string a2  in
             (match uu____8489 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____8502 =
                    let uu____8503 = e_list e_string  in
                    embed uu____8503 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____8502
              | uu____8513 -> FStar_Pervasives_Native.None)
         | uu____8517 -> FStar_Pervasives_Native.None)
    | uu____8523 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8556 =
          let uu____8566 = arg_as_string a1  in
          let uu____8570 = arg_as_int a2  in (uu____8566, uu____8570)  in
        (match uu____8556 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1040_8594  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____8599 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8599) ()
              with | uu___1039_8602 -> FStar_Pervasives_Native.None)
         | uu____8605 -> FStar_Pervasives_Native.None)
    | uu____8615 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8648 =
          let uu____8659 = arg_as_string a1  in
          let uu____8663 = arg_as_char a2  in (uu____8659, uu____8663)  in
        (match uu____8648 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1058_8692  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____8696 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8696) ()
              with | uu___1057_8698 -> FStar_Pervasives_Native.None)
         | uu____8701 -> FStar_Pervasives_Native.None)
    | uu____8712 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::a3::[] ->
        let uu____8754 =
          let uu____8768 = arg_as_string a1  in
          let uu____8772 = arg_as_int a2  in
          let uu____8775 = arg_as_int a3  in
          (uu____8768, uu____8772, uu____8775)  in
        (match uu____8754 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1081_8808  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____8813 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8813) ()
              with | uu___1080_8816 -> FStar_Pervasives_Native.None)
         | uu____8819 -> FStar_Pervasives_Native.None)
    | uu____8833 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8893 =
          let uu____8915 = arg_as_string fn  in
          let uu____8919 = arg_as_int from_line  in
          let uu____8922 = arg_as_int from_col  in
          let uu____8925 = arg_as_int to_line  in
          let uu____8928 = arg_as_int to_col  in
          (uu____8915, uu____8919, uu____8922, uu____8925, uu____8928)  in
        (match uu____8893 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8963 =
                 let uu____8964 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8966 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8964 uu____8966  in
               let uu____8968 =
                 let uu____8969 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8971 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8969 uu____8971  in
               FStar_Range.mk_range fn1 uu____8963 uu____8968  in
             let uu____8973 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8973
         | uu____8974 -> FStar_Pervasives_Native.None)
    | uu____8996 -> FStar_Pervasives_Native.None
  
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
                let uu____9086 = FStar_List.splitAt n_tvars args1  in
                match uu____9086 with
                | (_tvar_args,rest_args) ->
                    let uu____9135 = FStar_List.hd rest_args  in
                    (match uu____9135 with
                     | (x,uu____9147) ->
                         let uu____9148 = unembed ea cb x  in
                         FStar_Util.map_opt uu____9148
                           (fun x1  ->
                              let uu____9154 = f x1  in
                              embed eb cb uu____9154))
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
                  let uu____9263 = FStar_List.splitAt n_tvars args1  in
                  match uu____9263 with
                  | (_tvar_args,rest_args) ->
                      let uu____9312 = FStar_List.hd rest_args  in
                      (match uu____9312 with
                       | (x,uu____9324) ->
                           let uu____9325 =
                             let uu____9330 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____9330  in
                           (match uu____9325 with
                            | (y,uu____9348) ->
                                let uu____9349 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____9349
                                  (fun x1  ->
                                     let uu____9355 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____9355
                                       (fun y1  ->
                                          let uu____9361 =
                                            let uu____9362 = f x1 y1  in
                                            embed ec cb uu____9362  in
                                          FStar_Pervasives_Native.Some
                                            uu____9361))))
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
                    let uu____9490 = FStar_List.splitAt n_tvars args1  in
                    match uu____9490 with
                    | (_tvar_args,rest_args) ->
                        let uu____9539 = FStar_List.hd rest_args  in
                        (match uu____9539 with
                         | (x,uu____9551) ->
                             let uu____9552 =
                               let uu____9557 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____9557  in
                             (match uu____9552 with
                              | (y,uu____9575) ->
                                  let uu____9576 =
                                    let uu____9581 =
                                      let uu____9588 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____9588  in
                                    FStar_List.hd uu____9581  in
                                  (match uu____9576 with
                                   | (z,uu____9610) ->
                                       let uu____9611 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____9611
                                         (fun x1  ->
                                            let uu____9617 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____9617
                                              (fun y1  ->
                                                 let uu____9623 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____9623
                                                   (fun z1  ->
                                                      let uu____9629 =
                                                        let uu____9630 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____9630
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____9629))))))
                     in
                  f_wrapped
  