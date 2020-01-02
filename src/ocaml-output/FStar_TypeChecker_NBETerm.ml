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
  | Match of (t * (t -> t) *
  ((t -> FStar_Syntax_Syntax.term) -> FStar_Syntax_Syntax.branch Prims.list)) 
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
  
  | UnreducedLet of (var * t * t * t * FStar_Syntax_Syntax.letbinding) 
  | UnreducedLetRec of ((var * t * t) Prims.list * t *
  FStar_Syntax_Syntax.letbinding Prims.list) 
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
    match projectee with | Var _0 -> true | uu____607 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____643 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____745 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (t Prims.list -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____870 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____933 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____1008 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____1069 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____1088 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1107 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1125 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____1157 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____1250 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1311 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1334 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1379 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Thunk.t))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_TopLevelRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelRec _0 -> true | uu____1458 -> false
  
let (__proj__TopLevelRec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool Prims.list * (t
      * FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | TopLevelRec _0 -> _0 
let (uu___is_LocalLetRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalLetRec _0 -> true | uu____1560 -> false
  
let (__proj__LocalLetRec__item___0 :
  t ->
    (Prims.int * FStar_Syntax_Syntax.letbinding *
      FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool
      Prims.list))
  = fun projectee  -> match projectee with | LocalLetRec _0 -> _0 
let (uu___is_UnreducedLet : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLet _0 -> true | uu____1676 -> false
  
let (__proj__UnreducedLet__item___0 :
  t -> (var * t * t * t * FStar_Syntax_Syntax.letbinding)) =
  fun projectee  -> match projectee with | UnreducedLet _0 -> _0 
let (uu___is_UnreducedLetRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLetRec _0 -> true | uu____1741 -> false
  
let (__proj__UnreducedLetRec__item___0 :
  t ->
    ((var * t * t) Prims.list * t * FStar_Syntax_Syntax.letbinding
      Prims.list))
  = fun projectee  -> match projectee with | UnreducedLetRec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1814 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1857 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1894 -> false
  
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
    match projectee with | TOTAL  -> true | uu____2023 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____2034 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____2045 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____2056 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____2067 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____2078 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____2089 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____2100 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____2111 -> false 
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____2123 -> false
  
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
  fun trm  -> match trm with | Accu uu____2199 -> true | uu____2211 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____2221,uu____2222) -> false | uu____2236 -> true
  
let (mkConstruct :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i  -> fun us  -> fun ts  -> Construct (i, us, ts) 
let (mkFV :
  FStar_Syntax_Syntax.fv ->
    FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  = fun i  -> fun us  -> fun ts  -> FV (i, us, ts) 
let (mkAccuVar : var -> t) = fun v1  -> Accu ((Var v1), []) 
let (mkAccuMatch :
  t ->
    (t -> t) ->
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)
        -> t)
  = fun s  -> fun cases  -> fun bs  -> Accu ((Match (s, cases, bs)), []) 
let (equal_if : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___0_2372  ->
    if uu___0_2372
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2383  ->
    if uu___1_2383
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
      | (FStar_Syntax_Util.NotEqual ,uu____2399) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2400,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____2401) -> FStar_Syntax_Util.Unknown
      | (uu____2402,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____2419 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____2439),String (s2,uu____2441)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2454,uu____2455) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____2491,Lam uu____2492) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2585 = eq_atom a1 a2  in
          eq_and uu____2585 (fun uu____2587  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2626 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2626
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2642 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____2699  ->
                        match uu____2699 with
                        | ((a1,uu____2713),(a2,uu____2715)) ->
                            let uu____2724 = eq_t a1 a2  in
                            eq_inj acc uu____2724) FStar_Syntax_Util.Equal)
                uu____2642))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____2765 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2765
          then
            let uu____2768 =
              let uu____2769 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____2769  in
            eq_and uu____2768 (fun uu____2772  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____2779 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2779
      | (Univ u1,Univ u2) ->
          let uu____2783 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2783
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2830 =
            let uu____2831 =
              let uu____2832 = t11 ()  in
              FStar_Pervasives_Native.fst uu____2832  in
            let uu____2837 =
              let uu____2838 = t21 ()  in
              FStar_Pervasives_Native.fst uu____2838  in
            eq_t uu____2831 uu____2837  in
          eq_and uu____2830
            (fun uu____2846  ->
               let uu____2847 =
                 let uu____2848 = mkAccuVar x  in r1 uu____2848  in
               let uu____2849 =
                 let uu____2850 = mkAccuVar x  in r2 uu____2850  in
               eq_t uu____2847 uu____2849)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____2851,uu____2852) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____2857,uu____2858) -> FStar_Syntax_Util.Unknown

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
          let uu____2939 = eq_arg x y  in
          eq_and uu____2939 (fun uu____2941  -> eq_args xs ys)
      | (uu____2942,uu____2943) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2990) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2995 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2995
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____3014) ->
        let uu____3063 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____3074 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____3063 uu____3074
    | Accu (a,l) ->
        let uu____3091 =
          let uu____3093 = atom_to_string a  in
          let uu____3095 =
            let uu____3097 =
              let uu____3099 =
                let uu____3101 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____3101  in
              FStar_String.op_Hat uu____3099 ")"  in
            FStar_String.op_Hat ") (" uu____3097  in
          FStar_String.op_Hat uu____3093 uu____3095  in
        FStar_String.op_Hat "Accu (" uu____3091
    | Construct (fv,us,l) ->
        let uu____3139 =
          let uu____3141 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3143 =
            let uu____3145 =
              let uu____3147 =
                let uu____3149 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3149  in
              let uu____3155 =
                let uu____3157 =
                  let uu____3159 =
                    let uu____3161 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3161  in
                  FStar_String.op_Hat uu____3159 "]"  in
                FStar_String.op_Hat "] [" uu____3157  in
              FStar_String.op_Hat uu____3147 uu____3155  in
            FStar_String.op_Hat ") [" uu____3145  in
          FStar_String.op_Hat uu____3141 uu____3143  in
        FStar_String.op_Hat "Construct (" uu____3139
    | FV (fv,us,l) ->
        let uu____3200 =
          let uu____3202 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3204 =
            let uu____3206 =
              let uu____3208 =
                let uu____3210 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3210  in
              let uu____3216 =
                let uu____3218 =
                  let uu____3220 =
                    let uu____3222 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3222  in
                  FStar_String.op_Hat uu____3220 "]"  in
                FStar_String.op_Hat "] [" uu____3218  in
              FStar_String.op_Hat uu____3208 uu____3216  in
            FStar_String.op_Hat ") [" uu____3206  in
          FStar_String.op_Hat uu____3202 uu____3204  in
        FStar_String.op_Hat "FV (" uu____3200
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____3244 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____3244
    | Type_t u ->
        let uu____3248 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____3248
    | Arrow uu____3251 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____3297 = t ()  in FStar_Pervasives_Native.fst uu____3297
           in
        let uu____3302 =
          let uu____3304 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____3306 =
            let uu____3308 =
              let uu____3310 = t_to_string t1  in
              let uu____3312 =
                let uu____3314 =
                  let uu____3316 =
                    let uu____3318 =
                      let uu____3319 = mkAccuVar x1  in f uu____3319  in
                    t_to_string uu____3318  in
                  FStar_String.op_Hat uu____3316 "}"  in
                FStar_String.op_Hat "{" uu____3314  in
              FStar_String.op_Hat uu____3310 uu____3312  in
            FStar_String.op_Hat ":" uu____3308  in
          FStar_String.op_Hat uu____3304 uu____3306  in
        FStar_String.op_Hat "Refinement " uu____3302
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____3326 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____3326
    | Quote uu____3329 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____3336) ->
        let uu____3353 =
          let uu____3355 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____3355  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3353
    | Lazy (FStar_Util.Inr (uu____3357,et),uu____3359) ->
        let uu____3376 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3376
    | LocalLetRec
        (uu____3379,l,uu____3381,uu____3382,uu____3383,uu____3384,uu____3385)
        ->
        let uu____3416 =
          let uu____3418 = FStar_Syntax_Print.lbs_to_string [] (true, [l])
             in
          FStar_String.op_Hat uu____3418 ")"  in
        FStar_String.op_Hat "LocalLetRec (" uu____3416
    | TopLevelRec (lb,uu____3427,uu____3428,uu____3429) ->
        let uu____3450 =
          let uu____3452 =
            let uu____3454 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3454  in
          FStar_String.op_Hat uu____3452 ")"  in
        FStar_String.op_Hat "TopLevelRec (" uu____3450

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____3460 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____3460
    | Match (t,uu____3464,uu____3465) ->
        let uu____3488 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____3488

let (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____3498 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____3498 t_to_string
  
let (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____3511 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____3511 (FStar_String.concat " ")
  
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
        let uu____3982 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____3982 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____4003 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____4003 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____4044  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____4059  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____4102 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____4102
         then
           let uu____4126 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____4126
         else ());
        (let uu____4131 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____4131
         then f ()
         else
           (let thunk1 = FStar_Thunk.mk f  in
            let li = let uu____4165 = FStar_Dyn.mkdyn x  in (uu____4165, et)
               in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____4193 'a .
    'Auu____4193 ->
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
              let uu____4244 = FStar_Thunk.force thunk1  in f uu____4244
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____4264 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____4264
              then
                let res =
                  let uu____4293 = FStar_Thunk.force thunk1  in f uu____4293
                   in
                ((let uu____4295 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4295
                  then
                    let uu____4319 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____4321 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____4319
                      uu____4321
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____4330 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4330
                  then
                    let uu____4354 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____4354
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____4359 ->
              let aopt = f x  in
              ((let uu____4364 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____4364
                then
                  let uu____4388 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4388
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
  let uu____4456 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____4456 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____4490 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____4495 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4490 uu____4495 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____4536 -> FStar_Pervasives_Native.None  in
  let uu____4538 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____4543 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4538 uu____4543 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____4585 -> FStar_Pervasives_Native.None  in
  let uu____4587 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____4592 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____4587 uu____4592 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____4634)) -> FStar_Pervasives_Native.Some s1
    | uu____4638 -> FStar_Pervasives_Native.None  in
  let uu____4640 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____4645 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____4640 uu____4645 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____4680 -> FStar_Pervasives_Native.None  in
  let uu____4681 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____4686 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____4681 uu____4686 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____4707 =
        let uu____4715 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____4715, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4707  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____4740  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____4741 =
                 let uu____4742 =
                   let uu____4747 = type_of ea  in as_iarg uu____4747  in
                 [uu____4742]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4741
           | FStar_Pervasives_Native.Some x ->
               let uu____4757 =
                 let uu____4758 =
                   let uu____4763 = embed ea cb x  in as_arg uu____4763  in
                 let uu____4764 =
                   let uu____4771 =
                     let uu____4776 = type_of ea  in as_iarg uu____4776  in
                   [uu____4771]  in
                 uu____4758 :: uu____4764  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4757)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____4843)::uu____4844::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____4871 = unembed ea cb a  in
               FStar_Util.bind_opt uu____4871
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____4880 -> FStar_Pervasives_Native.None)
       in
    let uu____4883 =
      let uu____4884 =
        let uu____4885 = let uu____4890 = type_of ea  in as_arg uu____4890
           in
        [uu____4885]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____4884
       in
    mk_emb em un uu____4883 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4937 =
          let uu____4945 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____4945, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4937  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____4976  ->
             let uu____4977 =
               let uu____4978 =
                 let uu____4983 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____4983  in
               let uu____4984 =
                 let uu____4991 =
                   let uu____4996 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____4996  in
                 let uu____4997 =
                   let uu____5004 =
                     let uu____5009 = type_of eb  in as_iarg uu____5009  in
                   let uu____5010 =
                     let uu____5017 =
                       let uu____5022 = type_of ea  in as_iarg uu____5022  in
                     [uu____5017]  in
                   uu____5004 :: uu____5010  in
                 uu____4991 :: uu____4997  in
               uu____4978 :: uu____4984  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____4977)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____5090)::(a,uu____5092)::uu____5093::uu____5094::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____5133 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____5133
                   (fun a1  ->
                      let uu____5143 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____5143
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____5156 -> FStar_Pervasives_Native.None)
         in
      let uu____5161 =
        let uu____5162 =
          let uu____5163 = let uu____5168 = type_of eb  in as_arg uu____5168
             in
          let uu____5169 =
            let uu____5176 =
              let uu____5181 = type_of ea  in as_arg uu____5181  in
            [uu____5176]  in
          uu____5163 :: uu____5169  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5162
         in
      mk_emb em un uu____5161 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5234 =
          let uu____5242 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____5242, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5234  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____5274  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____5276 =
                   let uu____5277 =
                     let uu____5282 = embed ea cb a  in as_arg uu____5282  in
                   let uu____5283 =
                     let uu____5290 =
                       let uu____5295 = type_of eb  in as_iarg uu____5295  in
                     let uu____5296 =
                       let uu____5303 =
                         let uu____5308 = type_of ea  in as_iarg uu____5308
                          in
                       [uu____5303]  in
                     uu____5290 :: uu____5296  in
                   uu____5277 :: uu____5283  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5276
             | FStar_Util.Inr b ->
                 let uu____5326 =
                   let uu____5327 =
                     let uu____5332 = embed eb cb b  in as_arg uu____5332  in
                   let uu____5333 =
                     let uu____5340 =
                       let uu____5345 = type_of eb  in as_iarg uu____5345  in
                     let uu____5346 =
                       let uu____5353 =
                         let uu____5358 = type_of ea  in as_iarg uu____5358
                          in
                       [uu____5353]  in
                     uu____5340 :: uu____5346  in
                   uu____5327 :: uu____5333  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5326)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____5420)::uu____5421::uu____5422::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____5457 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____5457
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____5473)::uu____5474::uu____5475::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____5510 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____5510
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____5523 -> FStar_Pervasives_Native.None)
         in
      let uu____5528 =
        let uu____5529 =
          let uu____5530 = let uu____5535 = type_of eb  in as_arg uu____5535
             in
          let uu____5536 =
            let uu____5543 =
              let uu____5548 = type_of ea  in as_arg uu____5548  in
            [uu____5543]  in
          uu____5530 :: uu____5536  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5529
         in
      mk_emb em un uu____5528 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____5597 -> FStar_Pervasives_Native.None  in
  let uu____5598 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____5603 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____5598 uu____5603 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____5624 =
        let uu____5632 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____5632, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5624  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____5659  ->
           let typ = let uu____5661 = type_of ea  in as_iarg uu____5661  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____5682 =
               let uu____5683 = as_arg tl1  in
               let uu____5688 =
                 let uu____5695 =
                   let uu____5700 = embed ea cb hd1  in as_arg uu____5700  in
                 [uu____5695; typ]  in
               uu____5683 :: uu____5688  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____5682
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____5748,uu____5749) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____5769,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____5772,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5773))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5801 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5801
                 (fun hd2  ->
                    let uu____5809 = un cb tl1  in
                    FStar_Util.bind_opt uu____5809
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____5825,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5850 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5850
                 (fun hd2  ->
                    let uu____5858 = un cb tl1  in
                    FStar_Util.bind_opt uu____5858
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____5873 -> FStar_Pervasives_Native.None)
       in
    let uu____5876 =
      let uu____5877 =
        let uu____5878 = let uu____5883 = type_of ea  in as_arg uu____5883
           in
        [uu____5878]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____5877
       in
    mk_emb em un uu____5876 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____5956  ->
             Lam
               ((fun tas  ->
                   let uu____5988 =
                     let uu____5991 = FStar_List.hd tas  in
                     unembed ea cb uu____5991  in
                   match uu____5988 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____5993 = f a  in embed eb cb uu____5993
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____6006  ->
                     let uu____6009 = type_of eb  in as_arg uu____6009)],
                 Prims.int_one, FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____6069 =
                 let uu____6072 =
                   let uu____6073 =
                     let uu____6074 =
                       let uu____6079 = embed ea cb x  in as_arg uu____6079
                        in
                     [uu____6074]  in
                   cb.iapp lam1 uu____6073  in
                 unembed eb cb uu____6072  in
               match uu____6069 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____6093 =
        let uu____6094 = type_of ea  in
        let uu____6095 = let uu____6096 = type_of eb  in as_iarg uu____6096
           in
        make_arrow1 uu____6094 uu____6095  in
      mk_emb em un uu____6093 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____6114 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6114 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____6119 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6119 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____6124 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6124 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____6129 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6129 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____6134 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6134 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____6139 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6139 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____6144 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6144 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____6149 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6149 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____6154 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6154 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____6163 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6164 =
          let uu____6165 =
            let uu____6170 =
              let uu____6171 = e_list e_string  in embed uu____6171 cb l  in
            as_arg uu____6170  in
          [uu____6165]  in
        mkFV uu____6163 [] uu____6164
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____6193 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6194 =
          let uu____6195 =
            let uu____6200 =
              let uu____6201 = e_list e_string  in embed uu____6201 cb l  in
            as_arg uu____6200  in
          [uu____6195]  in
        mkFV uu____6193 [] uu____6194
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____6223 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6224 =
          let uu____6225 =
            let uu____6230 =
              let uu____6231 = e_list e_string  in embed uu____6231 cb l  in
            as_arg uu____6230  in
          [uu____6225]  in
        mkFV uu____6223 [] uu____6224
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____6265,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____6281,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____6297,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____6313,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____6329,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____6345,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____6361,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____6377,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____6393,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____6409,(l,uu____6411)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____6430 =
          let uu____6436 = e_list e_string  in unembed uu____6436 cb l  in
        FStar_Util.bind_opt uu____6430
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6456  -> FStar_Pervasives_Native.Some _6456)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____6458,(l,uu____6460)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____6479 =
          let uu____6485 = e_list e_string  in unembed uu____6485 cb l  in
        FStar_Util.bind_opt uu____6479
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6505  -> FStar_Pervasives_Native.Some _6505)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____6507,(l,uu____6509)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____6528 =
          let uu____6534 = e_list e_string  in unembed uu____6534 cb l  in
        FStar_Util.bind_opt uu____6528
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6554  -> FStar_Pervasives_Native.Some _6554)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____6555 ->
        ((let uu____6557 =
            let uu____6563 =
              let uu____6565 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____6565
               in
            (FStar_Errors.Warning_NotEmbedded, uu____6563)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____6557);
         FStar_Pervasives_Native.None)
     in
  let uu____6569 =
    let uu____6570 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____6570 [] []  in
  let uu____6575 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____6569 uu____6575 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____6584  -> failwith "bogus_cbs translate")
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
      let uu____6661 =
        let uu____6670 = e_list e  in unembed uu____6670 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6661
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____6692  ->
    match uu____6692 with
    | (a,uu____6700) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____6715)::[]) when
             let uu____6732 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6732 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____6739 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____6782 = let uu____6789 = as_arg c  in [uu____6789]  in
      int_to_t2 uu____6782
  
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
          let uu____6843 = f a  in FStar_Pervasives_Native.Some uu____6843
      | uu____6844 -> FStar_Pervasives_Native.None
  
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
          let uu____6898 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____6898
      | uu____6899 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6943 = FStar_List.map as_a args  in lift_unary f uu____6943
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6998 = FStar_List.map as_a args  in
        lift_binary f uu____6998
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____7028 = f x  in embed e_int bogus_cbs uu____7028)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____7055 = f x y  in embed e_int bogus_cbs uu____7055)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____7081 = f x  in embed e_bool bogus_cbs uu____7081)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____7119 = f x y  in embed e_bool bogus_cbs uu____7119)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____7157 = f x y  in embed e_string bogus_cbs uu____7157)
  
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
                let uu____7262 =
                  let uu____7271 = as_a a  in
                  let uu____7274 = as_b b  in (uu____7271, uu____7274)  in
                (match uu____7262 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____7289 =
                       let uu____7290 = f a1 b1  in embed_c uu____7290  in
                     FStar_Pervasives_Native.Some uu____7289
                 | uu____7291 -> FStar_Pervasives_Native.None)
            | uu____7300 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____7309 = e_list e_char  in
    let uu____7316 = FStar_String.list_of_string s  in
    embed uu____7309 bogus_cbs uu____7316
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____7355 =
        let uu____7356 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____7356  in
      embed e_int bogus_cbs uu____7355
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7390 = arg_as_string a1  in
        (match uu____7390 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7399 = arg_as_list e_string a2  in
             (match uu____7399 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7417 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7417
              | uu____7419 -> FStar_Pervasives_Native.None)
         | uu____7425 -> FStar_Pervasives_Native.None)
    | uu____7429 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____7436 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____7436
  
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
      | (_typ,uu____7498)::(a1,uu____7500)::(a2,uu____7502)::[] ->
          let uu____7519 = eq_t a1 a2  in
          (match uu____7519 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____7528 -> FStar_Pervasives_Native.None)
      | uu____7529 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7544)::(_typ,uu____7546)::(a1,uu____7548)::(a2,uu____7550)::[]
        ->
        let uu____7571 = eq_t a1 a2  in
        (match uu____7571 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7574 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7574
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7577 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7577
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7580 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7595)::(_v,uu____7597)::(t1,uu____7599)::(t2,uu____7601)::
        (a1,uu____7603)::(a2,uu____7605)::[] ->
        let uu____7634 =
          let uu____7635 = eq_t t1 t2  in
          let uu____7636 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____7635 uu____7636  in
        (match uu____7634 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7639 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7639
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7642 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7642
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7645 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____7664 =
        let uu____7666 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____7666  in
      failwith uu____7664
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____7682)::[] ->
        let uu____7691 = unembed e_range bogus_cbs a1  in
        (match uu____7691 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7697 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____7697
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7698 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7734 = arg_as_list e_char a1  in
        (match uu____7734 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7750 = arg_as_string a2  in
             (match uu____7750 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____7763 =
                    let uu____7764 = e_list e_string  in
                    embed uu____7764 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7763
              | uu____7774 -> FStar_Pervasives_Native.None)
         | uu____7778 -> FStar_Pervasives_Native.None)
    | uu____7784 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7817 =
          let uu____7827 = arg_as_string a1  in
          let uu____7831 = arg_as_int a2  in (uu____7827, uu____7831)  in
        (match uu____7817 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___990_7855  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____7860 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7860) ()
              with | uu___989_7863 -> FStar_Pervasives_Native.None)
         | uu____7866 -> FStar_Pervasives_Native.None)
    | uu____7876 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7909 =
          let uu____7920 = arg_as_string a1  in
          let uu____7924 = arg_as_char a2  in (uu____7920, uu____7924)  in
        (match uu____7909 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1008_7953  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____7957 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7957) ()
              with | uu___1007_7959 -> FStar_Pervasives_Native.None)
         | uu____7962 -> FStar_Pervasives_Native.None)
    | uu____7973 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____8015 =
          let uu____8029 = arg_as_string a1  in
          let uu____8033 = arg_as_int a2  in
          let uu____8036 = arg_as_int a3  in
          (uu____8029, uu____8033, uu____8036)  in
        (match uu____8015 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1031_8069  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____8074 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____8074) ()
              with | uu___1030_8077 -> FStar_Pervasives_Native.None)
         | uu____8080 -> FStar_Pervasives_Native.None)
    | uu____8094 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8154 =
          let uu____8176 = arg_as_string fn  in
          let uu____8180 = arg_as_int from_line  in
          let uu____8183 = arg_as_int from_col  in
          let uu____8186 = arg_as_int to_line  in
          let uu____8189 = arg_as_int to_col  in
          (uu____8176, uu____8180, uu____8183, uu____8186, uu____8189)  in
        (match uu____8154 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8224 =
                 let uu____8225 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8227 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8225 uu____8227  in
               let uu____8229 =
                 let uu____8230 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8232 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8230 uu____8232  in
               FStar_Range.mk_range fn1 uu____8224 uu____8229  in
             let uu____8234 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8234
         | uu____8235 -> FStar_Pervasives_Native.None)
    | uu____8257 -> FStar_Pervasives_Native.None
  
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
                let uu____8347 = FStar_List.splitAt n_tvars args  in
                match uu____8347 with
                | (_tvar_args,rest_args) ->
                    let uu____8396 = FStar_List.hd rest_args  in
                    (match uu____8396 with
                     | (x,uu____8408) ->
                         let uu____8409 = unembed ea cb x  in
                         FStar_Util.map_opt uu____8409
                           (fun x1  ->
                              let uu____8415 = f x1  in
                              embed eb cb uu____8415))
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
                  let uu____8524 = FStar_List.splitAt n_tvars args  in
                  match uu____8524 with
                  | (_tvar_args,rest_args) ->
                      let uu____8573 = FStar_List.hd rest_args  in
                      (match uu____8573 with
                       | (x,uu____8585) ->
                           let uu____8586 =
                             let uu____8591 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____8591  in
                           (match uu____8586 with
                            | (y,uu____8609) ->
                                let uu____8610 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____8610
                                  (fun x1  ->
                                     let uu____8616 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____8616
                                       (fun y1  ->
                                          let uu____8622 =
                                            let uu____8623 = f x1 y1  in
                                            embed ec cb uu____8623  in
                                          FStar_Pervasives_Native.Some
                                            uu____8622))))
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
                    let uu____8751 = FStar_List.splitAt n_tvars args  in
                    match uu____8751 with
                    | (_tvar_args,rest_args) ->
                        let uu____8800 = FStar_List.hd rest_args  in
                        (match uu____8800 with
                         | (x,uu____8812) ->
                             let uu____8813 =
                               let uu____8818 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____8818  in
                             (match uu____8813 with
                              | (y,uu____8836) ->
                                  let uu____8837 =
                                    let uu____8842 =
                                      let uu____8849 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____8849  in
                                    FStar_List.hd uu____8842  in
                                  (match uu____8837 with
                                   | (z,uu____8871) ->
                                       let uu____8872 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____8872
                                         (fun x1  ->
                                            let uu____8878 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____8878
                                              (fun y1  ->
                                                 let uu____8884 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____8884
                                                   (fun z1  ->
                                                      let uu____8890 =
                                                        let uu____8891 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____8891
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____8890))))))
                     in
                  f_wrapped
  