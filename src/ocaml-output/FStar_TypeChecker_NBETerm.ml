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
  fun projectee  -> match projectee with | Unit  -> true | uu____62 -> false 
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____75 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Int _0 -> true | uu____97 -> false 
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____121 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____156 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____178 -> false
  
let (__proj__Range__item___0 : constant -> FStar_Range.range) =
  fun projectee  -> match projectee with | Range _0 -> _0 
let (uu___is_SConst : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | SConst _0 -> true | uu____197 -> false
  
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
and t =
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
  | TopLevelLet of (FStar_Syntax_Syntax.letbinding * Prims.int * (t *
  FStar_Syntax_Syntax.aqual) Prims.list) 
  | TopLevelRec of (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool
  Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | LocalLetRec of (Prims.int * FStar_Syntax_Syntax.letbinding *
  FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
  FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool Prims.list) 
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
    match projectee with | Var _0 -> true | uu____895 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____923 -> false
  
let (__proj__Match__item___0 :
  atom -> (t * (unit -> FStar_Syntax_Syntax.branch Prims.list))) =
  fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_UnreducedLet : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLet _0 -> true | uu____985 -> false
  
let (__proj__UnreducedLet__item___0 :
  atom ->
    (var * t FStar_Thunk.t * t FStar_Thunk.t * t FStar_Thunk.t *
      FStar_Syntax_Syntax.letbinding))
  = fun projectee  -> match projectee with | UnreducedLet _0 -> _0 
let (uu___is_UnreducedLetRec : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLetRec _0 -> true | uu____1068 -> false
  
let (__proj__UnreducedLetRec__item___0 :
  atom ->
    ((var * t * t) Prims.list * t * FStar_Syntax_Syntax.letbinding
      Prims.list))
  = fun projectee  -> match projectee with | UnreducedLetRec _0 -> _0 
let (uu___is_UVar : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UVar _0 -> true | uu____1137 -> false
  
let (__proj__UVar__item___0 : atom -> FStar_Syntax_Syntax.term FStar_Thunk.t)
  = fun projectee  -> match projectee with | UVar _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____1194 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) *
      ((t Prims.list * FStar_Syntax_Syntax.binders *
         FStar_Syntax_Syntax.residual_comp FStar_Pervasives_Native.option),
      (t * FStar_Syntax_Syntax.aqual) Prims.list) FStar_Util.either *
      Prims.int))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____1319 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____1382 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____1457 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____1518 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____1537 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1556 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1574 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____1602 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    (FStar_Syntax_Syntax.term FStar_Thunk.t,((t * FStar_Syntax_Syntax.aqual)
                                              Prims.list * comp))
      FStar_Util.either)
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____1683 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1744 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1767 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1812 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Thunk.t))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_TopLevelLet : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelLet _0 -> true | uu____1886 -> false
  
let (__proj__TopLevelLet__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | TopLevelLet _0 -> _0 
let (uu___is_TopLevelRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelRec _0 -> true | uu____1962 -> false
  
let (__proj__TopLevelRec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool Prims.list * (t
      * FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | TopLevelRec _0 -> _0 
let (uu___is_LocalLetRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalLetRec _0 -> true | uu____2064 -> false
  
let (__proj__LocalLetRec__item___0 :
  t ->
    (Prims.int * FStar_Syntax_Syntax.letbinding *
      FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool
      Prims.list))
  = fun projectee  -> match projectee with | LocalLetRec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____2176 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____2219 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____2256 -> false
  
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
    match projectee with | TOTAL  -> true | uu____2385 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____2396 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____2407 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____2418 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____2429 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____2440 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____2451 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____2462 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____2473 -> false 
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____2485 -> false
  
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
  fun trm  -> match trm with | Accu uu____2561 -> true | uu____2573 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____2583,uu____2584) -> false | uu____2598 -> true
  
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i  -> fun us  -> fun ts  -> Construct (i, us, ts) 
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i  -> fun us  -> fun ts  -> FV (i, us, ts) 
let (mkAccuVar : var -> t) = fun v  -> Accu ((Var v), []) 
let (mkAccuMatch : t -> (unit -> FStar_Syntax_Syntax.branch Prims.list) -> t)
  = fun s  -> fun bs  -> Accu ((Match (s, bs)), []) 
let (equal_if : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___0_2713  ->
    if uu___0_2713
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2724  ->
    if uu___1_2724
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
      | (FStar_Syntax_Util.NotEqual ,uu____2740) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2741,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____2742) -> FStar_Syntax_Util.Unknown
      | (uu____2743,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____2760 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____2780),String (s2,uu____2782)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2795,uu____2796) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____2832,Lam uu____2833) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2926 = eq_atom a1 a2  in
          eq_and uu____2926 (fun uu____2928  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2967 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2967
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2983 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____3040  ->
                        match uu____3040 with
                        | ((a1,uu____3054),(a2,uu____3056)) ->
                            let uu____3065 = eq_t a1 a2  in
                            eq_inj acc uu____3065) FStar_Syntax_Util.Equal)
                uu____2983))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____3106 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____3106
          then
            let uu____3109 =
              let uu____3110 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____3110  in
            eq_and uu____3109 (fun uu____3113  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____3120 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____3120
      | (Univ u1,Univ u2) ->
          let uu____3124 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____3124
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____3171 =
            let uu____3172 =
              let uu____3173 = t11 ()  in
              FStar_Pervasives_Native.fst uu____3173  in
            let uu____3178 =
              let uu____3179 = t21 ()  in
              FStar_Pervasives_Native.fst uu____3179  in
            eq_t uu____3172 uu____3178  in
          eq_and uu____3171
            (fun uu____3187  ->
               let uu____3188 =
                 let uu____3189 = mkAccuVar x  in r1 uu____3189  in
               let uu____3190 =
                 let uu____3191 = mkAccuVar x  in r2 uu____3191  in
               eq_t uu____3188 uu____3190)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____3192,uu____3193) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) ->
          let uu____3198 = FStar_Syntax_Syntax.bv_eq bv1 bv2  in
          equal_if uu____3198
      | (uu____3200,uu____3201) -> FStar_Syntax_Util.Unknown

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
          let uu____3282 = eq_arg x y  in
          eq_and uu____3282 (fun uu____3284  -> eq_args xs ys)
      | (uu____3285,uu____3286) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____3333) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____3338 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____3338
    | SConst s -> FStar_Syntax_Print.const_to_string s
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,uu____3356,arity) ->
        let uu____3410 = FStar_Util.string_of_int arity  in
        FStar_Util.format1 "Lam (_, %s args)" uu____3410
    | Accu (a,l) ->
        let uu____3427 =
          let uu____3429 = atom_to_string a  in
          let uu____3431 =
            let uu____3433 =
              let uu____3435 =
                let uu____3437 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____3437  in
              FStar_String.op_Hat uu____3435 ")"  in
            FStar_String.op_Hat ") (" uu____3433  in
          FStar_String.op_Hat uu____3429 uu____3431  in
        FStar_String.op_Hat "Accu (" uu____3427
    | Construct (fv,us,l) ->
        let uu____3475 =
          let uu____3477 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3479 =
            let uu____3481 =
              let uu____3483 =
                let uu____3485 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3485  in
              let uu____3491 =
                let uu____3493 =
                  let uu____3495 =
                    let uu____3497 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3497  in
                  FStar_String.op_Hat uu____3495 "]"  in
                FStar_String.op_Hat "] [" uu____3493  in
              FStar_String.op_Hat uu____3483 uu____3491  in
            FStar_String.op_Hat ") [" uu____3481  in
          FStar_String.op_Hat uu____3477 uu____3479  in
        FStar_String.op_Hat "Construct (" uu____3475
    | FV (fv,us,l) ->
        let uu____3536 =
          let uu____3538 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3540 =
            let uu____3542 =
              let uu____3544 =
                let uu____3546 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3546  in
              let uu____3552 =
                let uu____3554 =
                  let uu____3556 =
                    let uu____3558 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3558  in
                  FStar_String.op_Hat uu____3556 "]"  in
                FStar_String.op_Hat "] [" uu____3554  in
              FStar_String.op_Hat uu____3544 uu____3552  in
            FStar_String.op_Hat ") [" uu____3542  in
          FStar_String.op_Hat uu____3538 uu____3540  in
        FStar_String.op_Hat "FV (" uu____3536
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____3580 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____3580
    | Type_t u ->
        let uu____3584 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____3584
    | Arrow uu____3587 -> "Arrow"
    | Refinement (f,t1) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t2 =
          let uu____3629 = t1 ()  in FStar_Pervasives_Native.fst uu____3629
           in
        let uu____3634 =
          let uu____3636 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____3638 =
            let uu____3640 =
              let uu____3642 = t_to_string t2  in
              let uu____3644 =
                let uu____3646 =
                  let uu____3648 =
                    let uu____3650 =
                      let uu____3651 = mkAccuVar x1  in f uu____3651  in
                    t_to_string uu____3650  in
                  FStar_String.op_Hat uu____3648 "}"  in
                FStar_String.op_Hat "{" uu____3646  in
              FStar_String.op_Hat uu____3642 uu____3644  in
            FStar_String.op_Hat ":" uu____3640  in
          FStar_String.op_Hat uu____3636 uu____3638  in
        FStar_String.op_Hat "Refinement " uu____3634
    | Unknown  -> "Unknown"
    | Reflect t1 ->
        let uu____3658 = t_to_string t1  in
        FStar_String.op_Hat "Reflect " uu____3658
    | Quote uu____3661 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____3668) ->
        let uu____3685 =
          let uu____3687 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____3687  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3685
    | Lazy (FStar_Util.Inr (uu____3689,et),uu____3691) ->
        let uu____3708 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3708
    | LocalLetRec
        (uu____3711,l,uu____3713,uu____3714,uu____3715,uu____3716,uu____3717)
        ->
        let uu____3748 =
          let uu____3750 = FStar_Syntax_Print.lbs_to_string [] (true, [l])
             in
          FStar_String.op_Hat uu____3750 ")"  in
        FStar_String.op_Hat "LocalLetRec (" uu____3748
    | TopLevelLet (lb,uu____3759,uu____3760) ->
        let uu____3775 =
          let uu____3777 =
            let uu____3779 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3779  in
          FStar_String.op_Hat uu____3777 ")"  in
        FStar_String.op_Hat "TopLevelLet (" uu____3775
    | TopLevelRec (lb,uu____3783,uu____3784,uu____3785) ->
        let uu____3806 =
          let uu____3808 =
            let uu____3810 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3810  in
          FStar_String.op_Hat uu____3808 ")"  in
        FStar_String.op_Hat "TopLevelRec (" uu____3806

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v ->
        let uu____3816 = FStar_Syntax_Print.bv_to_string v  in
        FStar_String.op_Hat "Var " uu____3816
    | Match (t1,uu____3820) ->
        let uu____3831 = t_to_string t1  in
        FStar_String.op_Hat "Match " uu____3831
    | UnreducedLet (var1,typ,def,body,lb) ->
        let uu____3851 =
          let uu____3853 = FStar_Syntax_Print.lbs_to_string [] (false, [lb])
             in
          FStar_String.op_Hat uu____3853 " in ...)"  in
        FStar_String.op_Hat "UnreducedLet(" uu____3851
    | UnreducedLetRec (uu____3861,body,lbs) ->
        let uu____3884 =
          let uu____3886 = FStar_Syntax_Print.lbs_to_string [] (true, lbs)
             in
          let uu____3892 =
            let uu____3894 =
              let uu____3896 = t_to_string body  in
              FStar_String.op_Hat uu____3896 ")"  in
            FStar_String.op_Hat " in " uu____3894  in
          FStar_String.op_Hat uu____3886 uu____3892  in
        FStar_String.op_Hat "UnreducedLetRec(" uu____3884
    | UVar uu____3901 -> "UVar"

let (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____3912 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____3912 t_to_string
  
let (args_to_string : args -> Prims.string) =
  fun args1  ->
    let uu____3925 =
      FStar_All.pipe_right args1 (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____3925 (FStar_String.concat " ")
  
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
               fun x  -> let uu____4436 = ba x  in embed ea cbs uu____4436)
            (fun cbs  ->
               fun t1  ->
                 let uu____4442 = unembed ea cbs t1  in
                 FStar_Util.map_opt uu____4442 ab)
            (match ot with
             | FStar_Pervasives_Native.Some t1 -> t1
             | FStar_Pervasives_Native.None  -> ea.typ) ea.emb_typ
  
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args1  ->
        let uu____4467 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____4467 us args1
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args1  ->
        let uu____4488 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____4488 us args1
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow (FStar_Util.Inr ([a], (Tot (t1, FStar_Pervasives_Native.None))))
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____4571 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____4571
         then
           let uu____4595 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____4595
         else ());
        (let uu____4600 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____4600
         then f ()
         else
           (let thunk = FStar_Thunk.mk f  in
            let li = let uu____4634 = FStar_Dyn.mkdyn x  in (uu____4634, et)
               in
            Lazy ((FStar_Util.Inr li), thunk)))
  
let lazy_unembed :
  'uuuuuu4662 'a .
    'uuuuuu4662 ->
      FStar_Syntax_Syntax.emb_typ ->
        t ->
          (t -> 'a FStar_Pervasives_Native.option) ->
            'a FStar_Pervasives_Native.option
  =
  fun cb  ->
    fun et  ->
      fun x  ->
        fun f  ->
          match x with
          | Lazy (FStar_Util.Inl li,thunk) ->
              let uu____4713 = FStar_Thunk.force thunk  in f uu____4713
          | Lazy (FStar_Util.Inr (b,et'),thunk) ->
              let uu____4733 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____4733
              then
                let res =
                  let uu____4762 = FStar_Thunk.force thunk  in f uu____4762
                   in
                ((let uu____4764 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4764
                  then
                    let uu____4788 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____4790 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____4788
                      uu____4790
                  else ());
                 res)
              else
                (let a1 = FStar_Dyn.undyn b  in
                 (let uu____4799 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4799
                  then
                    let uu____4823 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____4823
                  else ());
                 FStar_Pervasives_Native.Some a1)
          | uu____4828 ->
              let aopt = f x  in
              ((let uu____4833 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____4833
                then
                  let uu____4857 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4857
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
  let uu____4925 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____4925 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t1 = FStar_Pervasives_Native.Some ()  in
  let uu____4959 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____4964 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4959 uu____4964 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t1 =
    match t1 with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____5005 -> FStar_Pervasives_Native.None  in
  let uu____5007 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____5012 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____5007 uu____5012 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____5054 -> FStar_Pervasives_Native.None  in
  let uu____5056 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____5061 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____5056 uu____5061 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____5103)) -> FStar_Pervasives_Native.Some s1
    | uu____5107 -> FStar_Pervasives_Native.None  in
  let uu____5109 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____5114 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____5109 uu____5114 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____5149 -> FStar_Pervasives_Native.None  in
  let uu____5150 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____5155 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____5150 uu____5155 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____5176 =
        let uu____5184 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____5184, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5176  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____5209  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____5210 =
                 let uu____5211 =
                   let uu____5216 = type_of ea  in as_iarg uu____5216  in
                 [uu____5211]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____5210
           | FStar_Pervasives_Native.Some x ->
               let uu____5226 =
                 let uu____5227 =
                   let uu____5232 = embed ea cb x  in as_arg uu____5232  in
                 let uu____5233 =
                   let uu____5240 =
                     let uu____5245 = type_of ea  in as_iarg uu____5245  in
                   [uu____5240]  in
                 uu____5227 :: uu____5233  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____5226)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar,us,args1) when
               FStar_Syntax_Syntax.fv_eq_lid fvar FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar,us,(a1,uu____5312)::uu____5313::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar FStar_Parser_Const.some_lid
               ->
               let uu____5340 = unembed ea cb a1  in
               FStar_Util.bind_opt uu____5340
                 (fun a2  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a2))
           | uu____5349 -> FStar_Pervasives_Native.None)
       in
    let uu____5352 =
      let uu____5353 =
        let uu____5354 = let uu____5359 = type_of ea  in as_arg uu____5359
           in
        [uu____5354]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____5353
       in
    mk_emb em un uu____5352 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5406 =
          let uu____5414 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____5414, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5406  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____5445  ->
             let uu____5446 =
               let uu____5447 =
                 let uu____5452 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____5452  in
               let uu____5453 =
                 let uu____5460 =
                   let uu____5465 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____5465  in
                 let uu____5466 =
                   let uu____5473 =
                     let uu____5478 = type_of eb  in as_iarg uu____5478  in
                   let uu____5479 =
                     let uu____5486 =
                       let uu____5491 = type_of ea  in as_iarg uu____5491  in
                     [uu____5486]  in
                   uu____5473 :: uu____5479  in
                 uu____5460 :: uu____5466  in
               uu____5447 :: uu____5453  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____5446)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar,us,(b1,uu____5559)::(a1,uu____5561)::uu____5562::uu____5563::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____5602 = unembed ea cb a1  in
                 FStar_Util.bind_opt uu____5602
                   (fun a2  ->
                      let uu____5612 = unembed eb cb b1  in
                      FStar_Util.bind_opt uu____5612
                        (fun b2  -> FStar_Pervasives_Native.Some (a2, b2)))
             | uu____5625 -> FStar_Pervasives_Native.None)
         in
      let uu____5630 =
        let uu____5631 =
          let uu____5632 = let uu____5637 = type_of eb  in as_arg uu____5637
             in
          let uu____5638 =
            let uu____5645 =
              let uu____5650 = type_of ea  in as_arg uu____5650  in
            [uu____5645]  in
          uu____5632 :: uu____5638  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5631
         in
      mk_emb em un uu____5630 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5703 =
          let uu____5711 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____5711, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5703  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____5743  ->
             match s with
             | FStar_Util.Inl a1 ->
                 let uu____5745 =
                   let uu____5746 =
                     let uu____5751 = embed ea cb a1  in as_arg uu____5751
                      in
                   let uu____5752 =
                     let uu____5759 =
                       let uu____5764 = type_of eb  in as_iarg uu____5764  in
                     let uu____5765 =
                       let uu____5772 =
                         let uu____5777 = type_of ea  in as_iarg uu____5777
                          in
                       [uu____5772]  in
                     uu____5759 :: uu____5765  in
                   uu____5746 :: uu____5752  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5745
             | FStar_Util.Inr b1 ->
                 let uu____5795 =
                   let uu____5796 =
                     let uu____5801 = embed eb cb b1  in as_arg uu____5801
                      in
                   let uu____5802 =
                     let uu____5809 =
                       let uu____5814 = type_of eb  in as_iarg uu____5814  in
                     let uu____5815 =
                       let uu____5822 =
                         let uu____5827 = type_of ea  in as_iarg uu____5827
                          in
                       [uu____5822]  in
                     uu____5809 :: uu____5815  in
                   uu____5796 :: uu____5802  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5795)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar,us,(a1,uu____5889)::uu____5890::uu____5891::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____5926 = unembed ea cb a1  in
                 FStar_Util.bind_opt uu____5926
                   (fun a2  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a2))
             | Construct
                 (fvar,us,(b1,uu____5942)::uu____5943::uu____5944::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____5979 = unembed eb cb b1  in
                 FStar_Util.bind_opt uu____5979
                   (fun b2  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b2))
             | uu____5992 -> FStar_Pervasives_Native.None)
         in
      let uu____5997 =
        let uu____5998 =
          let uu____5999 = let uu____6004 = type_of eb  in as_arg uu____6004
             in
          let uu____6005 =
            let uu____6012 =
              let uu____6017 = type_of ea  in as_arg uu____6017  in
            [uu____6012]  in
          uu____5999 :: uu____6005  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5998
         in
      mk_emb em un uu____5997 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t1 =
    match t1 with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____6066 -> FStar_Pervasives_Native.None  in
  let uu____6067 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____6072 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____6067 uu____6072 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____6093 =
        let uu____6101 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____6101, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____6093  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____6128  ->
           let typ = let uu____6130 = type_of ea  in as_iarg uu____6130  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons hd tl =
             let uu____6151 =
               let uu____6152 = as_arg tl  in
               let uu____6157 =
                 let uu____6164 =
                   let uu____6169 = embed ea cb hd  in as_arg uu____6169  in
                 [uu____6164; typ]  in
               uu____6152 :: uu____6157  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____6151
              in
           FStar_List.fold_right cons l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____6217,uu____6218) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____6238,(tl,FStar_Pervasives_Native.None )::(hd,FStar_Pervasives_Native.None
                                                                   )::
                (uu____6241,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____6242))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____6270 = unembed ea cb hd  in
               FStar_Util.bind_opt uu____6270
                 (fun hd1  ->
                    let uu____6278 = un cb tl  in
                    FStar_Util.bind_opt uu____6278
                      (fun tl1  -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | Construct
               (fv,uu____6294,(tl,FStar_Pervasives_Native.None )::(hd,FStar_Pervasives_Native.None
                                                                   )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____6319 = unembed ea cb hd  in
               FStar_Util.bind_opt uu____6319
                 (fun hd1  ->
                    let uu____6327 = un cb tl  in
                    FStar_Util.bind_opt uu____6327
                      (fun tl1  -> FStar_Pervasives_Native.Some (hd1 :: tl1)))
           | uu____6342 -> FStar_Pervasives_Native.None)
       in
    let uu____6345 =
      let uu____6346 =
        let uu____6347 = let uu____6352 = type_of ea  in as_arg uu____6352
           in
        [uu____6347]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____6346
       in
    mk_emb em un uu____6345 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____6426  ->
             let uu____6427 =
               let uu____6460 =
                 let uu____6481 =
                   let uu____6488 =
                     let uu____6493 = type_of eb  in as_arg uu____6493  in
                   [uu____6488]  in
                 FStar_Util.Inr uu____6481  in
               ((fun tas  ->
                   let uu____6551 =
                     let uu____6554 = FStar_List.hd tas  in
                     unembed ea cb uu____6554  in
                   match uu____6551 with
                   | FStar_Pervasives_Native.Some a1 ->
                       let uu____6556 = f a1  in embed eb cb uu____6556
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 uu____6460, Prims.int_one)
                in
             Lam uu____6427)
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____6603 =
                 let uu____6606 =
                   let uu____6607 =
                     let uu____6608 =
                       let uu____6613 = embed ea cb x  in as_arg uu____6613
                        in
                     [uu____6608]  in
                   cb.iapp lam1 uu____6607  in
                 unembed eb cb uu____6606  in
               match uu____6603 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____6627 =
        let uu____6628 = type_of ea  in
        let uu____6629 = let uu____6630 = type_of eb  in as_iarg uu____6630
           in
        make_arrow1 uu____6628 uu____6629  in
      mk_emb em un uu____6627 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n =
    match n with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____6648 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6648 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____6653 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6653 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____6658 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6658 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____6663 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6663 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____6668 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6668 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____6673 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6673 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____6678 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6678 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____6683 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6683 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____6688 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6688 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____6697 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6698 =
          let uu____6699 =
            let uu____6704 =
              let uu____6705 = e_list e_string  in embed uu____6705 cb l  in
            as_arg uu____6704  in
          [uu____6699]  in
        mkFV uu____6697 [] uu____6698
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____6727 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6728 =
          let uu____6729 =
            let uu____6734 =
              let uu____6735 = e_list e_string  in embed uu____6735 cb l  in
            as_arg uu____6734  in
          [uu____6729]  in
        mkFV uu____6727 [] uu____6728
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____6757 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6758 =
          let uu____6759 =
            let uu____6764 =
              let uu____6765 = e_list e_string  in embed uu____6765 cb l  in
            as_arg uu____6764  in
          [uu____6759]  in
        mkFV uu____6757 [] uu____6758
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____6799,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____6815,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____6831,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____6847,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____6863,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____6879,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____6895,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____6911,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____6927,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____6943,(l,uu____6945)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____6964 =
          let uu____6970 = e_list e_string  in unembed uu____6970 cb l  in
        FStar_Util.bind_opt uu____6964
          (fun ss  ->
             FStar_All.pipe_left
               (fun uu____6990  -> FStar_Pervasives_Native.Some uu____6990)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____6992,(l,uu____6994)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____7013 =
          let uu____7019 = e_list e_string  in unembed uu____7019 cb l  in
        FStar_Util.bind_opt uu____7013
          (fun ss  ->
             FStar_All.pipe_left
               (fun uu____7039  -> FStar_Pervasives_Native.Some uu____7039)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____7041,(l,uu____7043)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____7062 =
          let uu____7068 = e_list e_string  in unembed uu____7068 cb l  in
        FStar_Util.bind_opt uu____7062
          (fun ss  ->
             FStar_All.pipe_left
               (fun uu____7088  -> FStar_Pervasives_Native.Some uu____7088)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____7089 ->
        ((let uu____7091 =
            let uu____7097 =
              let uu____7099 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____7099
               in
            (FStar_Errors.Warning_NotEmbedded, uu____7097)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____7091);
         FStar_Pervasives_Native.None)
     in
  let uu____7103 =
    let uu____7104 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____7104 [] []  in
  let uu____7109 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____7103 uu____7109 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____7118  -> failwith "bogus_cbs translate")
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
      let uu____7195 =
        let uu____7204 = e_list e  in unembed uu____7204 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a1) uu____7195
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____7226  ->
    match uu____7226 with
    | (a,uu____7234) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____7249)::[]) when
             let uu____7266 =
               FStar_Ident.string_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____7266 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____7273 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t  ->
    fun n  ->
      let c = embed e_int bogus_cbs n  in
      let int_to_t1 args1 = FV (int_to_t, [], args1)  in
      let uu____7316 = let uu____7323 = as_arg c  in [uu____7323]  in
      int_to_t1 uu____7316
  
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
          let uu____7377 = f a1  in FStar_Pervasives_Native.Some uu____7377
      | uu____7378 -> FStar_Pervasives_Native.None
  
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
          let uu____7432 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____7432
      | uu____7433 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args1  ->
        let uu____7477 = FStar_List.map as_a args1  in
        lift_unary f uu____7477
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args1  ->
        let uu____7532 = FStar_List.map as_a args1  in
        lift_binary f uu____7532
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____7562 = f x  in embed e_int bogus_cbs uu____7562)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____7589 = f x y  in embed e_int bogus_cbs uu____7589)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____7615 = f x  in embed e_bool bogus_cbs uu____7615)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____7653 = f x y  in embed e_bool bogus_cbs uu____7653)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____7691 = f x y  in embed e_string bogus_cbs uu____7691)
  
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
                let uu____7796 =
                  let uu____7805 = as_a a1  in
                  let uu____7808 = as_b b1  in (uu____7805, uu____7808)  in
                (match uu____7796 with
                 | (FStar_Pervasives_Native.Some
                    a2,FStar_Pervasives_Native.Some b2) ->
                     let uu____7823 =
                       let uu____7824 = f a2 b2  in embed_c uu____7824  in
                     FStar_Pervasives_Native.Some uu____7823
                 | uu____7825 -> FStar_Pervasives_Native.None)
            | uu____7834 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____7843 = e_list e_char  in
    let uu____7850 = FStar_String.list_of_string s  in
    embed uu____7843 bogus_cbs uu____7850
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____7889 =
        let uu____7890 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____7890  in
      embed e_int bogus_cbs uu____7889
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____7924 = arg_as_string a1  in
        (match uu____7924 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7933 = arg_as_list e_string a2  in
             (match uu____7933 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7951 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7951
              | uu____7953 -> FStar_Pervasives_Native.None)
         | uu____7959 -> FStar_Pervasives_Native.None)
    | uu____7963 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____7970 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____7970
  
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
      | (_typ,uu____8032)::(a1,uu____8034)::(a2,uu____8036)::[] ->
          let uu____8053 = eq_t a1 a2  in
          (match uu____8053 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____8062 -> FStar_Pervasives_Native.None)
      | uu____8063 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | (_u,uu____8078)::(_typ,uu____8080)::(a1,uu____8082)::(a2,uu____8084)::[]
        ->
        let uu____8105 = eq_t a1 a2  in
        (match uu____8105 with
         | FStar_Syntax_Util.Equal  ->
             let uu____8108 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____8108
         | FStar_Syntax_Util.NotEqual  ->
             let uu____8111 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____8111
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____8114 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | (_u,uu____8129)::(_v,uu____8131)::(t1,uu____8133)::(t2,uu____8135)::
        (a1,uu____8137)::(a2,uu____8139)::[] ->
        let uu____8168 =
          let uu____8169 = eq_t t1 t2  in
          let uu____8170 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____8169 uu____8170  in
        (match uu____8168 with
         | FStar_Syntax_Util.Equal  ->
             let uu____8173 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____8173
         | FStar_Syntax_Util.NotEqual  ->
             let uu____8176 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____8176
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____8179 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args1  ->
      let uu____8198 =
        let uu____8200 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____8200  in
      failwith uu____8198
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | (a1,uu____8216)::[] ->
        let uu____8225 = unembed e_range bogus_cbs a1  in
        (match uu____8225 with
         | FStar_Pervasives_Native.Some r ->
             let uu____8231 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8231
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____8232 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8268 = arg_as_list e_char a1  in
        (match uu____8268 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____8284 = arg_as_string a2  in
             (match uu____8284 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____8297 =
                    let uu____8298 = e_list e_string  in
                    embed uu____8298 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____8297
              | uu____8308 -> FStar_Pervasives_Native.None)
         | uu____8312 -> FStar_Pervasives_Native.None)
    | uu____8318 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8351 =
          let uu____8361 = arg_as_string a1  in
          let uu____8365 = arg_as_int a2  in (uu____8361, uu____8365)  in
        (match uu____8351 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1023_8389  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____8394 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8394) ()
              with | uu___1022_8397 -> FStar_Pervasives_Native.None)
         | uu____8400 -> FStar_Pervasives_Native.None)
    | uu____8410 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::[] ->
        let uu____8443 =
          let uu____8454 = arg_as_string a1  in
          let uu____8458 = arg_as_char a2  in (uu____8454, uu____8458)  in
        (match uu____8443 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1041_8487  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____8491 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8491) ()
              with | uu___1040_8493 -> FStar_Pervasives_Native.None)
         | uu____8496 -> FStar_Pervasives_Native.None)
    | uu____8507 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | a1::a2::a3::[] ->
        let uu____8549 =
          let uu____8563 = arg_as_string a1  in
          let uu____8567 = arg_as_int a2  in
          let uu____8570 = arg_as_int a3  in
          (uu____8563, uu____8567, uu____8570)  in
        (match uu____8549 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1064_8603  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____8608 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8608) ()
              with | uu___1063_8611 -> FStar_Pervasives_Native.None)
         | uu____8614 -> FStar_Pervasives_Native.None)
    | uu____8628 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args1  ->
    match args1 with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8688 =
          let uu____8710 = arg_as_string fn  in
          let uu____8714 = arg_as_int from_line  in
          let uu____8717 = arg_as_int from_col  in
          let uu____8720 = arg_as_int to_line  in
          let uu____8723 = arg_as_int to_col  in
          (uu____8710, uu____8714, uu____8717, uu____8720, uu____8723)  in
        (match uu____8688 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8758 =
                 let uu____8759 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8761 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8759 uu____8761  in
               let uu____8763 =
                 let uu____8764 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8766 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8764 uu____8766  in
               FStar_Range.mk_range fn1 uu____8758 uu____8763  in
             let uu____8768 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8768
         | uu____8769 -> FStar_Pervasives_Native.None)
    | uu____8791 -> FStar_Pervasives_Native.None
  
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
                let uu____8881 = FStar_List.splitAt n_tvars args1  in
                match uu____8881 with
                | (_tvar_args,rest_args) ->
                    let uu____8930 = FStar_List.hd rest_args  in
                    (match uu____8930 with
                     | (x,uu____8942) ->
                         let uu____8943 = unembed ea cb x  in
                         FStar_Util.map_opt uu____8943
                           (fun x1  ->
                              let uu____8949 = f x1  in
                              embed eb cb uu____8949))
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
                  let uu____9058 = FStar_List.splitAt n_tvars args1  in
                  match uu____9058 with
                  | (_tvar_args,rest_args) ->
                      let uu____9107 = FStar_List.hd rest_args  in
                      (match uu____9107 with
                       | (x,uu____9119) ->
                           let uu____9120 =
                             let uu____9125 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____9125  in
                           (match uu____9120 with
                            | (y,uu____9143) ->
                                let uu____9144 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____9144
                                  (fun x1  ->
                                     let uu____9150 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____9150
                                       (fun y1  ->
                                          let uu____9156 =
                                            let uu____9157 = f x1 y1  in
                                            embed ec cb uu____9157  in
                                          FStar_Pervasives_Native.Some
                                            uu____9156))))
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
                    let uu____9285 = FStar_List.splitAt n_tvars args1  in
                    match uu____9285 with
                    | (_tvar_args,rest_args) ->
                        let uu____9334 = FStar_List.hd rest_args  in
                        (match uu____9334 with
                         | (x,uu____9346) ->
                             let uu____9347 =
                               let uu____9352 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____9352  in
                             (match uu____9347 with
                              | (y,uu____9370) ->
                                  let uu____9371 =
                                    let uu____9376 =
                                      let uu____9383 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____9383  in
                                    FStar_List.hd uu____9376  in
                                  (match uu____9371 with
                                   | (z,uu____9405) ->
                                       let uu____9406 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____9406
                                         (fun x1  ->
                                            let uu____9412 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____9412
                                              (fun y1  ->
                                                 let uu____9418 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____9418
                                                   (fun z1  ->
                                                      let uu____9424 =
                                                        let uu____9425 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____9425
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____9424))))))
                     in
                  f_wrapped
  