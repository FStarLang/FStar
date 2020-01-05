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
let (uu___is_Unit : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Unit  -> true | uu____57 -> false 
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____70 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Int _0 -> true | uu____92 -> false 
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____116 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____151 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____173 -> false
  
let (__proj__Range__item___0 : constant -> FStar_Range.range) =
  fun projectee  -> match projectee with | Range _0 -> _0 
type atom =
  | Var of var 
  | Match of (t * (unit -> FStar_Syntax_Syntax.branch Prims.list)) 
  | UnreducedLet of (var * t FStar_Thunk.t * t FStar_Thunk.t * t
  FStar_Thunk.t * FStar_Syntax_Syntax.letbinding) 
  | UnreducedLetRec of ((var * t * t) Prims.list * t *
  FStar_Syntax_Syntax.letbinding Prims.list) 
and t =
  | Lam of ((t Prims.list -> t) *
  (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list * Prims.int *
  (t Prims.list -> residual_comp) FStar_Pervasives_Native.option) 
  | Accu of (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | Construct of (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe
  Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | FV of (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list *
  (t * FStar_Syntax_Syntax.aqual) Prims.list) 
  | Constant of constant 
  | Type_t of FStar_Syntax_Syntax.universe 
  | Univ of FStar_Syntax_Syntax.universe 
  | Unknown 
  | Arrow of ((t Prims.list -> comp) *
  (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list) 
  | Refinement of ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual))) 
  | Reflect of t 
  | Quote of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo) 
  | Lazy of
  ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                   FStar_Syntax_Syntax.emb_typ))
  FStar_Util.either * t FStar_Thunk.t) 
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
    match projectee with | Var _0 -> true | uu____660 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____688 -> false
  
let (__proj__Match__item___0 :
  atom -> (t * (unit -> FStar_Syntax_Syntax.branch Prims.list))) =
  fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_UnreducedLet : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLet _0 -> true | uu____750 -> false
  
let (__proj__UnreducedLet__item___0 :
  atom ->
    (var * t FStar_Thunk.t * t FStar_Thunk.t * t FStar_Thunk.t *
      FStar_Syntax_Syntax.letbinding))
  = fun projectee  -> match projectee with | UnreducedLet _0 -> _0 
let (uu___is_UnreducedLetRec : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLetRec _0 -> true | uu____833 -> false
  
let (__proj__UnreducedLetRec__item___0 :
  atom ->
    ((var * t * t) Prims.list * t * FStar_Syntax_Syntax.letbinding
      Prims.list))
  = fun projectee  -> match projectee with | UnreducedLetRec _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____932 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (t Prims.list -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____1057 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____1120 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____1195 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____1256 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____1275 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1294 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1312 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____1344 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____1437 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1498 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1521 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1566 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Thunk.t))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_TopLevelRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelRec _0 -> true | uu____1645 -> false
  
let (__proj__TopLevelRec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool Prims.list * (t
      * FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | TopLevelRec _0 -> _0 
let (uu___is_LocalLetRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalLetRec _0 -> true | uu____1747 -> false
  
let (__proj__LocalLetRec__item___0 :
  t ->
    (Prims.int * FStar_Syntax_Syntax.letbinding *
      FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool
      Prims.list))
  = fun projectee  -> match projectee with | LocalLetRec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1859 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1902 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1939 -> false
  
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
    match projectee with | TOTAL  -> true | uu____2068 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____2079 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____2090 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____2101 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____2112 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____2123 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____2134 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____2145 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____2156 -> false 
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____2168 -> false
  
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
  fun trm  -> match trm with | Accu uu____2244 -> true | uu____2256 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____2266,uu____2267) -> false | uu____2281 -> true
  
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i  -> fun us  -> fun ts  -> Construct (i, us, ts) 
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i  -> fun us  -> fun ts  -> FV (i, us, ts) 
let (mkAccuVar : var -> t) = fun v1  -> Accu ((Var v1), []) 
let (mkAccuMatch : t -> (unit -> FStar_Syntax_Syntax.branch Prims.list) -> t)
  = fun s  -> fun bs  -> Accu ((Match (s, bs)), []) 
let (equal_if : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___0_2396  ->
    if uu___0_2396
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2407  ->
    if uu___1_2407
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
      | (FStar_Syntax_Util.NotEqual ,uu____2423) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2424,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____2425) -> FStar_Syntax_Util.Unknown
      | (uu____2426,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____2443 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____2463),String (s2,uu____2465)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2478,uu____2479) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____2515,Lam uu____2516) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2609 = eq_atom a1 a2  in
          eq_and uu____2609 (fun uu____2611  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2650 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2650
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2666 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____2723  ->
                        match uu____2723 with
                        | ((a1,uu____2737),(a2,uu____2739)) ->
                            let uu____2748 = eq_t a1 a2  in
                            eq_inj acc uu____2748) FStar_Syntax_Util.Equal)
                uu____2666))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____2789 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2789
          then
            let uu____2792 =
              let uu____2793 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____2793  in
            eq_and uu____2792 (fun uu____2796  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____2803 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2803
      | (Univ u1,Univ u2) ->
          let uu____2807 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2807
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2854 =
            let uu____2855 =
              let uu____2856 = t11 ()  in
              FStar_Pervasives_Native.fst uu____2856  in
            let uu____2861 =
              let uu____2862 = t21 ()  in
              FStar_Pervasives_Native.fst uu____2862  in
            eq_t uu____2855 uu____2861  in
          eq_and uu____2854
            (fun uu____2870  ->
               let uu____2871 =
                 let uu____2872 = mkAccuVar x  in r1 uu____2872  in
               let uu____2873 =
                 let uu____2874 = mkAccuVar x  in r2 uu____2874  in
               eq_t uu____2871 uu____2873)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____2875,uu____2876) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____2881,uu____2882) -> FStar_Syntax_Util.Unknown

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
          let uu____2963 = eq_arg x y  in
          eq_and uu____2963 (fun uu____2965  -> eq_args xs ys)
      | (uu____2966,uu____2967) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____3014) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____3019 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____3019
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____3038) ->
        let uu____3087 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____3098 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____3087 uu____3098
    | Accu (a,l) ->
        let uu____3115 =
          let uu____3117 = atom_to_string a  in
          let uu____3119 =
            let uu____3121 =
              let uu____3123 =
                let uu____3125 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____3125  in
              FStar_String.op_Hat uu____3123 ")"  in
            FStar_String.op_Hat ") (" uu____3121  in
          FStar_String.op_Hat uu____3117 uu____3119  in
        FStar_String.op_Hat "Accu (" uu____3115
    | Construct (fv,us,l) ->
        let uu____3163 =
          let uu____3165 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3167 =
            let uu____3169 =
              let uu____3171 =
                let uu____3173 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3173  in
              let uu____3179 =
                let uu____3181 =
                  let uu____3183 =
                    let uu____3185 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3185  in
                  FStar_String.op_Hat uu____3183 "]"  in
                FStar_String.op_Hat "] [" uu____3181  in
              FStar_String.op_Hat uu____3171 uu____3179  in
            FStar_String.op_Hat ") [" uu____3169  in
          FStar_String.op_Hat uu____3165 uu____3167  in
        FStar_String.op_Hat "Construct (" uu____3163
    | FV (fv,us,l) ->
        let uu____3224 =
          let uu____3226 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3228 =
            let uu____3230 =
              let uu____3232 =
                let uu____3234 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3234  in
              let uu____3240 =
                let uu____3242 =
                  let uu____3244 =
                    let uu____3246 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3246  in
                  FStar_String.op_Hat uu____3244 "]"  in
                FStar_String.op_Hat "] [" uu____3242  in
              FStar_String.op_Hat uu____3232 uu____3240  in
            FStar_String.op_Hat ") [" uu____3230  in
          FStar_String.op_Hat uu____3226 uu____3228  in
        FStar_String.op_Hat "FV (" uu____3224
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____3268 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____3268
    | Type_t u ->
        let uu____3272 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____3272
    | Arrow uu____3275 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____3321 = t ()  in FStar_Pervasives_Native.fst uu____3321
           in
        let uu____3326 =
          let uu____3328 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____3330 =
            let uu____3332 =
              let uu____3334 = t_to_string t1  in
              let uu____3336 =
                let uu____3338 =
                  let uu____3340 =
                    let uu____3342 =
                      let uu____3343 = mkAccuVar x1  in f uu____3343  in
                    t_to_string uu____3342  in
                  FStar_String.op_Hat uu____3340 "}"  in
                FStar_String.op_Hat "{" uu____3338  in
              FStar_String.op_Hat uu____3334 uu____3336  in
            FStar_String.op_Hat ":" uu____3332  in
          FStar_String.op_Hat uu____3328 uu____3330  in
        FStar_String.op_Hat "Refinement " uu____3326
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____3350 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____3350
    | Quote uu____3353 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____3360) ->
        let uu____3377 =
          let uu____3379 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____3379  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3377
    | Lazy (FStar_Util.Inr (uu____3381,et),uu____3383) ->
        let uu____3400 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3400
    | LocalLetRec
        (uu____3403,l,uu____3405,uu____3406,uu____3407,uu____3408,uu____3409)
        ->
        let uu____3440 =
          let uu____3442 = FStar_Syntax_Print.lbs_to_string [] (true, [l])
             in
          FStar_String.op_Hat uu____3442 ")"  in
        FStar_String.op_Hat "LocalLetRec (" uu____3440
    | TopLevelRec (lb,uu____3451,uu____3452,uu____3453) ->
        let uu____3474 =
          let uu____3476 =
            let uu____3478 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3478  in
          FStar_String.op_Hat uu____3476 ")"  in
        FStar_String.op_Hat "TopLevelRec (" uu____3474

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____3484 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____3484
    | Match (t,uu____3488) ->
        let uu____3499 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____3499
    | UnreducedLet (var,typ,def,body,lb) ->
        let uu____3519 =
          let uu____3521 = FStar_Syntax_Print.lbs_to_string [] (false, [lb])
             in
          FStar_String.op_Hat uu____3521 " in ...)"  in
        FStar_String.op_Hat "UnreducedLet(" uu____3519
    | UnreducedLetRec (uu____3529,body,lbs) ->
        let uu____3552 =
          let uu____3554 = FStar_Syntax_Print.lbs_to_string [] (true, lbs)
             in
          let uu____3560 =
            let uu____3562 =
              let uu____3564 = t_to_string body  in
              FStar_String.op_Hat uu____3564 ")"  in
            FStar_String.op_Hat " in " uu____3562  in
          FStar_String.op_Hat uu____3554 uu____3560  in
        FStar_String.op_Hat "UnreducedLetRec(" uu____3552

let (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____3576 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____3576 t_to_string
  
let (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____3589 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____3589 (FStar_String.concat " ")
  
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
  fun cbs  -> fun t  -> cbs.translate t 
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
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____4060 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____4060 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____4081 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____4081 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____4122  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____4137  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____4180 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____4180
         then
           let uu____4204 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____4204
         else ());
        (let uu____4209 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____4209
         then f ()
         else
           (let thunk1 = FStar_Thunk.mk f  in
            let li = let uu____4243 = FStar_Dyn.mkdyn x  in (uu____4243, et)
               in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____4271 'a .
    'Auu____4271 ->
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
          | Lazy (FStar_Util.Inl li,thunk1) ->
              let uu____4322 = FStar_Thunk.force thunk1  in f uu____4322
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____4342 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____4342
              then
                let res =
                  let uu____4371 = FStar_Thunk.force thunk1  in f uu____4371
                   in
                ((let uu____4373 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4373
                  then
                    let uu____4397 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____4399 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____4397
                      uu____4399
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____4408 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4408
                  then
                    let uu____4432 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____4432
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____4437 ->
              let aopt = f x  in
              ((let uu____4442 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____4442
                then
                  let uu____4466 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4466
                else ());
               aopt)
  
let (mk_any_emb : t -> t embedding) =
  fun ty  ->
    let em _cb a = a  in
    let un _cb t = FStar_Pervasives_Native.Some t  in
    mk_emb em un ty FStar_Syntax_Syntax.ET_abstract
  
let (e_any : t embedding) =
  let em _cb a = a  in
  let un _cb t = FStar_Pervasives_Native.Some t  in
  let uu____4534 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____4534 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____4568 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____4573 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4568 uu____4573 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____4614 -> FStar_Pervasives_Native.None  in
  let uu____4616 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____4621 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4616 uu____4621 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____4663 -> FStar_Pervasives_Native.None  in
  let uu____4665 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____4670 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____4665 uu____4670 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____4712)) -> FStar_Pervasives_Native.Some s1
    | uu____4716 -> FStar_Pervasives_Native.None  in
  let uu____4718 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____4723 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____4718 uu____4723 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____4758 -> FStar_Pervasives_Native.None  in
  let uu____4759 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____4764 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____4759 uu____4764 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____4785 =
        let uu____4793 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____4793, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4785  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____4818  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____4819 =
                 let uu____4820 =
                   let uu____4825 = type_of ea  in as_iarg uu____4825  in
                 [uu____4820]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4819
           | FStar_Pervasives_Native.Some x ->
               let uu____4835 =
                 let uu____4836 =
                   let uu____4841 = embed ea cb x  in as_arg uu____4841  in
                 let uu____4842 =
                   let uu____4849 =
                     let uu____4854 = type_of ea  in as_iarg uu____4854  in
                   [uu____4849]  in
                 uu____4836 :: uu____4842  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4835)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____4921)::uu____4922::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____4949 = unembed ea cb a  in
               FStar_Util.bind_opt uu____4949
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____4958 -> FStar_Pervasives_Native.None)
       in
    let uu____4961 =
      let uu____4962 =
        let uu____4963 = let uu____4968 = type_of ea  in as_arg uu____4968
           in
        [uu____4963]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____4962
       in
    mk_emb em un uu____4961 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5015 =
          let uu____5023 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____5023, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5015  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____5054  ->
             let uu____5055 =
               let uu____5056 =
                 let uu____5061 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____5061  in
               let uu____5062 =
                 let uu____5069 =
                   let uu____5074 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____5074  in
                 let uu____5075 =
                   let uu____5082 =
                     let uu____5087 = type_of eb  in as_iarg uu____5087  in
                   let uu____5088 =
                     let uu____5095 =
                       let uu____5100 = type_of ea  in as_iarg uu____5100  in
                     [uu____5095]  in
                   uu____5082 :: uu____5088  in
                 uu____5069 :: uu____5075  in
               uu____5056 :: uu____5062  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____5055)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____5168)::(a,uu____5170)::uu____5171::uu____5172::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____5211 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____5211
                   (fun a1  ->
                      let uu____5221 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____5221
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____5234 -> FStar_Pervasives_Native.None)
         in
      let uu____5239 =
        let uu____5240 =
          let uu____5241 = let uu____5246 = type_of eb  in as_arg uu____5246
             in
          let uu____5247 =
            let uu____5254 =
              let uu____5259 = type_of ea  in as_arg uu____5259  in
            [uu____5254]  in
          uu____5241 :: uu____5247  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5240
         in
      mk_emb em un uu____5239 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5312 =
          let uu____5320 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____5320, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5312  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____5352  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____5354 =
                   let uu____5355 =
                     let uu____5360 = embed ea cb a  in as_arg uu____5360  in
                   let uu____5361 =
                     let uu____5368 =
                       let uu____5373 = type_of eb  in as_iarg uu____5373  in
                     let uu____5374 =
                       let uu____5381 =
                         let uu____5386 = type_of ea  in as_iarg uu____5386
                          in
                       [uu____5381]  in
                     uu____5368 :: uu____5374  in
                   uu____5355 :: uu____5361  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5354
             | FStar_Util.Inr b ->
                 let uu____5404 =
                   let uu____5405 =
                     let uu____5410 = embed eb cb b  in as_arg uu____5410  in
                   let uu____5411 =
                     let uu____5418 =
                       let uu____5423 = type_of eb  in as_iarg uu____5423  in
                     let uu____5424 =
                       let uu____5431 =
                         let uu____5436 = type_of ea  in as_iarg uu____5436
                          in
                       [uu____5431]  in
                     uu____5418 :: uu____5424  in
                   uu____5405 :: uu____5411  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5404)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____5498)::uu____5499::uu____5500::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____5535 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____5535
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____5551)::uu____5552::uu____5553::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____5588 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____5588
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____5601 -> FStar_Pervasives_Native.None)
         in
      let uu____5606 =
        let uu____5607 =
          let uu____5608 = let uu____5613 = type_of eb  in as_arg uu____5613
             in
          let uu____5614 =
            let uu____5621 =
              let uu____5626 = type_of ea  in as_arg uu____5626  in
            [uu____5621]  in
          uu____5608 :: uu____5614  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5607
         in
      mk_emb em un uu____5606 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____5675 -> FStar_Pervasives_Native.None  in
  let uu____5676 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____5681 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____5676 uu____5681 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____5702 =
        let uu____5710 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____5710, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5702  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____5737  ->
           let typ = let uu____5739 = type_of ea  in as_iarg uu____5739  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____5760 =
               let uu____5761 = as_arg tl1  in
               let uu____5766 =
                 let uu____5773 =
                   let uu____5778 = embed ea cb hd1  in as_arg uu____5778  in
                 [uu____5773; typ]  in
               uu____5761 :: uu____5766  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____5760
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____5826,uu____5827) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____5847,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____5850,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5851))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5879 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5879
                 (fun hd2  ->
                    let uu____5887 = un cb tl1  in
                    FStar_Util.bind_opt uu____5887
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____5903,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5928 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5928
                 (fun hd2  ->
                    let uu____5936 = un cb tl1  in
                    FStar_Util.bind_opt uu____5936
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____5951 -> FStar_Pervasives_Native.None)
       in
    let uu____5954 =
      let uu____5955 =
        let uu____5956 = let uu____5961 = type_of ea  in as_arg uu____5961
           in
        [uu____5956]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____5955
       in
    mk_emb em un uu____5954 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____6034  ->
             Lam
               ((fun tas  ->
                   let uu____6066 =
                     let uu____6069 = FStar_List.hd tas  in
                     unembed ea cb uu____6069  in
                   match uu____6066 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____6071 = f a  in embed eb cb uu____6071
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____6084  ->
                     let uu____6087 = type_of eb  in as_arg uu____6087)],
                 Prims.int_one, FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____6147 =
                 let uu____6150 =
                   let uu____6151 =
                     let uu____6152 =
                       let uu____6157 = embed ea cb x  in as_arg uu____6157
                        in
                     [uu____6152]  in
                   cb.iapp lam1 uu____6151  in
                 unembed eb cb uu____6150  in
               match uu____6147 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____6171 =
        let uu____6172 = type_of ea  in
        let uu____6173 = let uu____6174 = type_of eb  in as_iarg uu____6174
           in
        make_arrow1 uu____6172 uu____6173  in
      mk_emb em un uu____6171 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____6192 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6192 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____6197 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6197 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____6202 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6202 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____6207 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6207 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____6212 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6212 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____6217 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6217 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____6222 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6222 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____6227 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6227 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____6232 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6232 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____6241 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6242 =
          let uu____6243 =
            let uu____6248 =
              let uu____6249 = e_list e_string  in embed uu____6249 cb l  in
            as_arg uu____6248  in
          [uu____6243]  in
        mkFV uu____6241 [] uu____6242
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____6271 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6272 =
          let uu____6273 =
            let uu____6278 =
              let uu____6279 = e_list e_string  in embed uu____6279 cb l  in
            as_arg uu____6278  in
          [uu____6273]  in
        mkFV uu____6271 [] uu____6272
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____6301 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6302 =
          let uu____6303 =
            let uu____6308 =
              let uu____6309 = e_list e_string  in embed uu____6309 cb l  in
            as_arg uu____6308  in
          [uu____6303]  in
        mkFV uu____6301 [] uu____6302
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____6343,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____6359,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____6375,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____6391,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____6407,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____6423,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____6439,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____6455,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____6471,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____6487,(l,uu____6489)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____6508 =
          let uu____6514 = e_list e_string  in unembed uu____6514 cb l  in
        FStar_Util.bind_opt uu____6508
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6534  -> FStar_Pervasives_Native.Some _6534)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____6536,(l,uu____6538)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____6557 =
          let uu____6563 = e_list e_string  in unembed uu____6563 cb l  in
        FStar_Util.bind_opt uu____6557
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6583  -> FStar_Pervasives_Native.Some _6583)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____6585,(l,uu____6587)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____6606 =
          let uu____6612 = e_list e_string  in unembed uu____6612 cb l  in
        FStar_Util.bind_opt uu____6606
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6632  -> FStar_Pervasives_Native.Some _6632)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____6633 ->
        ((let uu____6635 =
            let uu____6641 =
              let uu____6643 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____6643
               in
            (FStar_Errors.Warning_NotEmbedded, uu____6641)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____6635);
         FStar_Pervasives_Native.None)
     in
  let uu____6647 =
    let uu____6648 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____6648 [] []  in
  let uu____6653 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____6647 uu____6653 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____6662  -> failwith "bogus_cbs translate")
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
    fun a  ->
      let uu____6739 =
        let uu____6748 = e_list e  in unembed uu____6748 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6739
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____6770  ->
    match uu____6770 with
    | (a,uu____6778) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____6793)::[]) when
             let uu____6810 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6810 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____6817 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____6860 = let uu____6867 = as_arg c  in [uu____6867]  in
      int_to_t2 uu____6860
  
let lift_unary :
  'a 'b .
    ('a -> 'b) ->
      'a FStar_Pervasives_Native.option Prims.list ->
        'b FStar_Pervasives_Native.option
  =
  fun f  ->
    fun aopts  ->
      match aopts with
      | (FStar_Pervasives_Native.Some a)::[] ->
          let uu____6921 = f a  in FStar_Pervasives_Native.Some uu____6921
      | uu____6922 -> FStar_Pervasives_Native.None
  
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
          let uu____6976 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____6976
      | uu____6977 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____7021 = FStar_List.map as_a args  in lift_unary f uu____7021
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____7076 = FStar_List.map as_a args  in
        lift_binary f uu____7076
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____7106 = f x  in embed e_int bogus_cbs uu____7106)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____7133 = f x y  in embed e_int bogus_cbs uu____7133)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____7159 = f x  in embed e_bool bogus_cbs uu____7159)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____7197 = f x y  in embed e_bool bogus_cbs uu____7197)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____7235 = f x y  in embed e_string bogus_cbs uu____7235)
  
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
          fun args  ->
            match args with
            | a::b::[] ->
                let uu____7340 =
                  let uu____7349 = as_a a  in
                  let uu____7352 = as_b b  in (uu____7349, uu____7352)  in
                (match uu____7340 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____7367 =
                       let uu____7368 = f a1 b1  in embed_c uu____7368  in
                     FStar_Pervasives_Native.Some uu____7367
                 | uu____7369 -> FStar_Pervasives_Native.None)
            | uu____7378 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____7387 = e_list e_char  in
    let uu____7394 = FStar_String.list_of_string s  in
    embed uu____7387 bogus_cbs uu____7394
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____7433 =
        let uu____7434 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____7434  in
      embed e_int bogus_cbs uu____7433
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7468 = arg_as_string a1  in
        (match uu____7468 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7477 = arg_as_list e_string a2  in
             (match uu____7477 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7495 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7495
              | uu____7497 -> FStar_Pervasives_Native.None)
         | uu____7503 -> FStar_Pervasives_Native.None)
    | uu____7507 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____7514 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____7514
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string bogus_cbs (if b then "true" else "false") 
let (string_lowercase : Prims.string -> t) =
  fun s  -> embed e_string bogus_cbs (FStar_String.lowercase s) 
let (string_uppercase : Prims.string -> t) =
  fun s  -> embed e_string bogus_cbs (FStar_String.lowercase s) 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool bogus_cbs true  in
      let fal = embed e_bool bogus_cbs false  in
      match args with
      | (_typ,uu____7576)::(a1,uu____7578)::(a2,uu____7580)::[] ->
          let uu____7597 = eq_t a1 a2  in
          (match uu____7597 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____7606 -> FStar_Pervasives_Native.None)
      | uu____7607 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7622)::(_typ,uu____7624)::(a1,uu____7626)::(a2,uu____7628)::[]
        ->
        let uu____7649 = eq_t a1 a2  in
        (match uu____7649 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7652 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7652
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7655 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7655
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7658 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7673)::(_v,uu____7675)::(t1,uu____7677)::(t2,uu____7679)::
        (a1,uu____7681)::(a2,uu____7683)::[] ->
        let uu____7712 =
          let uu____7713 = eq_t t1 t2  in
          let uu____7714 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____7713 uu____7714  in
        (match uu____7712 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7717 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7717
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7720 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7720
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7723 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____7742 =
        let uu____7744 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____7744  in
      failwith uu____7742
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____7760)::[] ->
        let uu____7769 = unembed e_range bogus_cbs a1  in
        (match uu____7769 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7775 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____7775
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7776 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7812 = arg_as_list e_char a1  in
        (match uu____7812 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7828 = arg_as_string a2  in
             (match uu____7828 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____7841 =
                    let uu____7842 = e_list e_string  in
                    embed uu____7842 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7841
              | uu____7852 -> FStar_Pervasives_Native.None)
         | uu____7856 -> FStar_Pervasives_Native.None)
    | uu____7862 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7895 =
          let uu____7905 = arg_as_string a1  in
          let uu____7909 = arg_as_int a2  in (uu____7905, uu____7909)  in
        (match uu____7895 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1000_7933  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____7938 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7938) ()
              with | uu___999_7941 -> FStar_Pervasives_Native.None)
         | uu____7944 -> FStar_Pervasives_Native.None)
    | uu____7954 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7987 =
          let uu____7998 = arg_as_string a1  in
          let uu____8002 = arg_as_char a2  in (uu____7998, uu____8002)  in
        (match uu____7987 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1018_8031  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____8035 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8035) ()
              with | uu___1017_8037 -> FStar_Pervasives_Native.None)
         | uu____8040 -> FStar_Pervasives_Native.None)
    | uu____8051 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____8093 =
          let uu____8107 = arg_as_string a1  in
          let uu____8111 = arg_as_int a2  in
          let uu____8114 = arg_as_int a3  in
          (uu____8107, uu____8111, uu____8114)  in
        (match uu____8093 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1041_8147  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____8152 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8152) ()
              with | uu___1040_8155 -> FStar_Pervasives_Native.None)
         | uu____8158 -> FStar_Pervasives_Native.None)
    | uu____8172 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8232 =
          let uu____8254 = arg_as_string fn  in
          let uu____8258 = arg_as_int from_line  in
          let uu____8261 = arg_as_int from_col  in
          let uu____8264 = arg_as_int to_line  in
          let uu____8267 = arg_as_int to_col  in
          (uu____8254, uu____8258, uu____8261, uu____8264, uu____8267)  in
        (match uu____8232 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8302 =
                 let uu____8303 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8305 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8303 uu____8305  in
               let uu____8307 =
                 let uu____8308 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8310 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8308 uu____8310  in
               FStar_Range.mk_range fn1 uu____8302 uu____8307  in
             let uu____8312 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8312
         | uu____8313 -> FStar_Pervasives_Native.None)
    | uu____8335 -> FStar_Pervasives_Native.None
  
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
              let f_wrapped args =
                let uu____8425 = FStar_List.splitAt n_tvars args  in
                match uu____8425 with
                | (_tvar_args,rest_args) ->
                    let uu____8474 = FStar_List.hd rest_args  in
                    (match uu____8474 with
                     | (x,uu____8486) ->
                         let uu____8487 = unembed ea cb x  in
                         FStar_Util.map_opt uu____8487
                           (fun x1  ->
                              let uu____8493 = f x1  in
                              embed eb cb uu____8493))
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
                let f_wrapped args =
                  let uu____8602 = FStar_List.splitAt n_tvars args  in
                  match uu____8602 with
                  | (_tvar_args,rest_args) ->
                      let uu____8651 = FStar_List.hd rest_args  in
                      (match uu____8651 with
                       | (x,uu____8663) ->
                           let uu____8664 =
                             let uu____8669 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____8669  in
                           (match uu____8664 with
                            | (y,uu____8687) ->
                                let uu____8688 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____8688
                                  (fun x1  ->
                                     let uu____8694 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____8694
                                       (fun y1  ->
                                          let uu____8700 =
                                            let uu____8701 = f x1 y1  in
                                            embed ec cb uu____8701  in
                                          FStar_Pervasives_Native.Some
                                            uu____8700))))
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
                  let f_wrapped args =
                    let uu____8829 = FStar_List.splitAt n_tvars args  in
                    match uu____8829 with
                    | (_tvar_args,rest_args) ->
                        let uu____8878 = FStar_List.hd rest_args  in
                        (match uu____8878 with
                         | (x,uu____8890) ->
                             let uu____8891 =
                               let uu____8896 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____8896  in
                             (match uu____8891 with
                              | (y,uu____8914) ->
                                  let uu____8915 =
                                    let uu____8920 =
                                      let uu____8927 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____8927  in
                                    FStar_List.hd uu____8920  in
                                  (match uu____8915 with
                                   | (z,uu____8949) ->
                                       let uu____8950 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____8950
                                         (fun x1  ->
                                            let uu____8956 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____8956
                                              (fun y1  ->
                                                 let uu____8962 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____8962
                                                   (fun z1  ->
                                                      let uu____8968 =
                                                        let uu____8969 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____8969
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____8968))))))
                     in
                  f_wrapped
  