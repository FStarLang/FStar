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
  
  | UnreducedLet of (var * t * t) 
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
    match projectee with | Var _0 -> true | uu____582 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____618 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____720 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (t Prims.list -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____845 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____908 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____983 -> false 
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____1044 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____1063 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1082 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1100 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____1132 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____1225 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1286 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1309 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1354 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Thunk.t))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_TopLevelRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | TopLevelRec _0 -> true | uu____1433 -> false
  
let (__proj__TopLevelRec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * Prims.int * Prims.bool Prims.list * (t
      * FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | TopLevelRec _0 -> _0 
let (uu___is_LocalLetRec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | LocalLetRec _0 -> true | uu____1535 -> false
  
let (__proj__LocalLetRec__item___0 :
  t ->
    (Prims.int * FStar_Syntax_Syntax.letbinding *
      FStar_Syntax_Syntax.letbinding Prims.list * t Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list * Prims.int * Prims.bool
      Prims.list))
  = fun projectee  -> match projectee with | LocalLetRec _0 -> _0 
let (uu___is_UnreducedLet : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | UnreducedLet _0 -> true | uu____1647 -> false
  
let (__proj__UnreducedLet__item___0 : t -> (var * t * t)) =
  fun projectee  -> match projectee with | UnreducedLet _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1690 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1733 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1770 -> false
  
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
    match projectee with | TOTAL  -> true | uu____1899 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____1910 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____1921 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____1932 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____1943 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____1954 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____1965 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____1976 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____1987 -> false 
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____1999 -> false
  
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
  fun trm  -> match trm with | Accu uu____2075 -> true | uu____2087 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____2097,uu____2098) -> false | uu____2112 -> true
  
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
  fun uu___0_2248  ->
    if uu___0_2248
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2259  ->
    if uu___1_2259
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
      | (FStar_Syntax_Util.NotEqual ,uu____2275) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2276,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____2277) -> FStar_Syntax_Util.Unknown
      | (uu____2278,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____2295 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____2315),String (s2,uu____2317)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2330,uu____2331) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____2367,Lam uu____2368) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2461 = eq_atom a1 a2  in
          eq_and uu____2461 (fun uu____2463  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2502 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2502
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2518 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____2575  ->
                        match uu____2575 with
                        | ((a1,uu____2589),(a2,uu____2591)) ->
                            let uu____2600 = eq_t a1 a2  in
                            eq_inj acc uu____2600) FStar_Syntax_Util.Equal)
                uu____2518))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____2641 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2641
          then
            let uu____2644 =
              let uu____2645 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____2645  in
            eq_and uu____2644 (fun uu____2648  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____2655 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2655
      | (Univ u1,Univ u2) ->
          let uu____2659 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2659
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2706 =
            let uu____2707 =
              let uu____2708 = t11 ()  in
              FStar_Pervasives_Native.fst uu____2708  in
            let uu____2713 =
              let uu____2714 = t21 ()  in
              FStar_Pervasives_Native.fst uu____2714  in
            eq_t uu____2707 uu____2713  in
          eq_and uu____2706
            (fun uu____2722  ->
               let uu____2723 =
                 let uu____2724 = mkAccuVar x  in r1 uu____2724  in
               let uu____2725 =
                 let uu____2726 = mkAccuVar x  in r2 uu____2726  in
               eq_t uu____2723 uu____2725)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____2727,uu____2728) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____2733,uu____2734) -> FStar_Syntax_Util.Unknown

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
          let uu____2815 = eq_arg x y  in
          eq_and uu____2815 (fun uu____2817  -> eq_args xs ys)
      | (uu____2818,uu____2819) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2866) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2871 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2871
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____2890) ->
        let uu____2939 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2950 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____2939 uu____2950
    | Accu (a,l) ->
        let uu____2967 =
          let uu____2969 = atom_to_string a  in
          let uu____2971 =
            let uu____2973 =
              let uu____2975 =
                let uu____2977 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2977  in
              FStar_String.op_Hat uu____2975 ")"  in
            FStar_String.op_Hat ") (" uu____2973  in
          FStar_String.op_Hat uu____2969 uu____2971  in
        FStar_String.op_Hat "Accu (" uu____2967
    | Construct (fv,us,l) ->
        let uu____3015 =
          let uu____3017 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3019 =
            let uu____3021 =
              let uu____3023 =
                let uu____3025 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3025  in
              let uu____3031 =
                let uu____3033 =
                  let uu____3035 =
                    let uu____3037 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3037  in
                  FStar_String.op_Hat uu____3035 "]"  in
                FStar_String.op_Hat "] [" uu____3033  in
              FStar_String.op_Hat uu____3023 uu____3031  in
            FStar_String.op_Hat ") [" uu____3021  in
          FStar_String.op_Hat uu____3017 uu____3019  in
        FStar_String.op_Hat "Construct (" uu____3015
    | FV (fv,us,l) ->
        let uu____3076 =
          let uu____3078 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____3080 =
            let uu____3082 =
              let uu____3084 =
                let uu____3086 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____3086  in
              let uu____3092 =
                let uu____3094 =
                  let uu____3096 =
                    let uu____3098 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____3098  in
                  FStar_String.op_Hat uu____3096 "]"  in
                FStar_String.op_Hat "] [" uu____3094  in
              FStar_String.op_Hat uu____3084 uu____3092  in
            FStar_String.op_Hat ") [" uu____3082  in
          FStar_String.op_Hat uu____3078 uu____3080  in
        FStar_String.op_Hat "FV (" uu____3076
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____3120 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____3120
    | Type_t u ->
        let uu____3124 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____3124
    | Arrow uu____3127 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____3173 = t ()  in FStar_Pervasives_Native.fst uu____3173
           in
        let uu____3178 =
          let uu____3180 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____3182 =
            let uu____3184 =
              let uu____3186 = t_to_string t1  in
              let uu____3188 =
                let uu____3190 =
                  let uu____3192 =
                    let uu____3194 =
                      let uu____3195 = mkAccuVar x1  in f uu____3195  in
                    t_to_string uu____3194  in
                  FStar_String.op_Hat uu____3192 "}"  in
                FStar_String.op_Hat "{" uu____3190  in
              FStar_String.op_Hat uu____3186 uu____3188  in
            FStar_String.op_Hat ":" uu____3184  in
          FStar_String.op_Hat uu____3180 uu____3182  in
        FStar_String.op_Hat "Refinement " uu____3178
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____3202 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____3202
    | Quote uu____3205 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____3212) ->
        let uu____3229 =
          let uu____3231 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____3231  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3229
    | Lazy (FStar_Util.Inr (uu____3233,et),uu____3235) ->
        let uu____3252 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3252
    | LocalLetRec
        (uu____3255,l,uu____3257,uu____3258,uu____3259,uu____3260,uu____3261)
        ->
        let uu____3292 =
          let uu____3294 = FStar_Syntax_Print.lbs_to_string [] (true, [l])
             in
          FStar_String.op_Hat uu____3294 ")"  in
        FStar_String.op_Hat "LocalLetRec (" uu____3292
    | TopLevelRec (lb,uu____3303,uu____3304,uu____3305) ->
        let uu____3326 =
          let uu____3328 =
            let uu____3330 = FStar_Util.right lb.FStar_Syntax_Syntax.lbname
               in
            FStar_Syntax_Print.fv_to_string uu____3330  in
          FStar_String.op_Hat uu____3328 ")"  in
        FStar_String.op_Hat "TopLevelRec (" uu____3326

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____3336 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____3336
    | Match (t,uu____3340,uu____3341) ->
        let uu____3364 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____3364

let (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____3374 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____3374 t_to_string
  
let (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____3387 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____3387 (FStar_String.concat " ")
  
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
        let uu____3858 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____3858 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____3879 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____3879 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____3920  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____3935  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____3978 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____3978
         then
           let uu____4002 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____4002
         else ());
        (let uu____4007 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____4007
         then f ()
         else
           (let thunk1 = FStar_Thunk.mk f  in
            let li = let uu____4041 = FStar_Dyn.mkdyn x  in (uu____4041, et)
               in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____4069 'a .
    'Auu____4069 ->
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
              let uu____4120 = FStar_Thunk.force thunk1  in f uu____4120
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____4140 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____4140
              then
                let res =
                  let uu____4169 = FStar_Thunk.force thunk1  in f uu____4169
                   in
                ((let uu____4171 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4171
                  then
                    let uu____4195 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____4197 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____4195
                      uu____4197
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____4206 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4206
                  then
                    let uu____4230 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____4230
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____4235 ->
              let aopt = f x  in
              ((let uu____4240 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____4240
                then
                  let uu____4264 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4264
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
  let uu____4332 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____4332 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____4366 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____4371 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4366 uu____4371 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____4412 -> FStar_Pervasives_Native.None  in
  let uu____4414 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____4419 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4414 uu____4419 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____4461 -> FStar_Pervasives_Native.None  in
  let uu____4463 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____4468 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____4463 uu____4468 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____4510)) -> FStar_Pervasives_Native.Some s1
    | uu____4514 -> FStar_Pervasives_Native.None  in
  let uu____4516 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____4521 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____4516 uu____4521 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____4556 -> FStar_Pervasives_Native.None  in
  let uu____4557 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____4562 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____4557 uu____4562 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____4583 =
        let uu____4591 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____4591, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4583  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____4616  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____4617 =
                 let uu____4618 =
                   let uu____4623 = type_of ea  in as_iarg uu____4623  in
                 [uu____4618]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4617
           | FStar_Pervasives_Native.Some x ->
               let uu____4633 =
                 let uu____4634 =
                   let uu____4639 = embed ea cb x  in as_arg uu____4639  in
                 let uu____4640 =
                   let uu____4647 =
                     let uu____4652 = type_of ea  in as_iarg uu____4652  in
                   [uu____4647]  in
                 uu____4634 :: uu____4640  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4633)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____4719)::uu____4720::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____4747 = unembed ea cb a  in
               FStar_Util.bind_opt uu____4747
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____4756 -> FStar_Pervasives_Native.None)
       in
    let uu____4759 =
      let uu____4760 =
        let uu____4761 = let uu____4766 = type_of ea  in as_arg uu____4766
           in
        [uu____4761]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____4760
       in
    mk_emb em un uu____4759 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4813 =
          let uu____4821 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____4821, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4813  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____4852  ->
             let uu____4853 =
               let uu____4854 =
                 let uu____4859 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____4859  in
               let uu____4860 =
                 let uu____4867 =
                   let uu____4872 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____4872  in
                 let uu____4873 =
                   let uu____4880 =
                     let uu____4885 = type_of eb  in as_iarg uu____4885  in
                   let uu____4886 =
                     let uu____4893 =
                       let uu____4898 = type_of ea  in as_iarg uu____4898  in
                     [uu____4893]  in
                   uu____4880 :: uu____4886  in
                 uu____4867 :: uu____4873  in
               uu____4854 :: uu____4860  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____4853)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____4966)::(a,uu____4968)::uu____4969::uu____4970::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____5009 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____5009
                   (fun a1  ->
                      let uu____5019 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____5019
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____5032 -> FStar_Pervasives_Native.None)
         in
      let uu____5037 =
        let uu____5038 =
          let uu____5039 = let uu____5044 = type_of eb  in as_arg uu____5044
             in
          let uu____5045 =
            let uu____5052 =
              let uu____5057 = type_of ea  in as_arg uu____5057  in
            [uu____5052]  in
          uu____5039 :: uu____5045  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5038
         in
      mk_emb em un uu____5037 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5110 =
          let uu____5118 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____5118, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5110  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____5150  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____5152 =
                   let uu____5153 =
                     let uu____5158 = embed ea cb a  in as_arg uu____5158  in
                   let uu____5159 =
                     let uu____5166 =
                       let uu____5171 = type_of eb  in as_iarg uu____5171  in
                     let uu____5172 =
                       let uu____5179 =
                         let uu____5184 = type_of ea  in as_iarg uu____5184
                          in
                       [uu____5179]  in
                     uu____5166 :: uu____5172  in
                   uu____5153 :: uu____5159  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5152
             | FStar_Util.Inr b ->
                 let uu____5202 =
                   let uu____5203 =
                     let uu____5208 = embed eb cb b  in as_arg uu____5208  in
                   let uu____5209 =
                     let uu____5216 =
                       let uu____5221 = type_of eb  in as_iarg uu____5221  in
                     let uu____5222 =
                       let uu____5229 =
                         let uu____5234 = type_of ea  in as_iarg uu____5234
                          in
                       [uu____5229]  in
                     uu____5216 :: uu____5222  in
                   uu____5203 :: uu____5209  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5202)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____5296)::uu____5297::uu____5298::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____5333 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____5333
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____5349)::uu____5350::uu____5351::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____5386 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____5386
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____5399 -> FStar_Pervasives_Native.None)
         in
      let uu____5404 =
        let uu____5405 =
          let uu____5406 = let uu____5411 = type_of eb  in as_arg uu____5411
             in
          let uu____5412 =
            let uu____5419 =
              let uu____5424 = type_of ea  in as_arg uu____5424  in
            [uu____5419]  in
          uu____5406 :: uu____5412  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5405
         in
      mk_emb em un uu____5404 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____5473 -> FStar_Pervasives_Native.None  in
  let uu____5474 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____5479 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____5474 uu____5479 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____5500 =
        let uu____5508 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____5508, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5500  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____5535  ->
           let typ = let uu____5537 = type_of ea  in as_iarg uu____5537  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____5558 =
               let uu____5559 = as_arg tl1  in
               let uu____5564 =
                 let uu____5571 =
                   let uu____5576 = embed ea cb hd1  in as_arg uu____5576  in
                 [uu____5571; typ]  in
               uu____5559 :: uu____5564  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____5558
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____5624,uu____5625) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____5645,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____5648,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5649))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5677 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5677
                 (fun hd2  ->
                    let uu____5685 = un cb tl1  in
                    FStar_Util.bind_opt uu____5685
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____5701,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5726 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5726
                 (fun hd2  ->
                    let uu____5734 = un cb tl1  in
                    FStar_Util.bind_opt uu____5734
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____5749 -> FStar_Pervasives_Native.None)
       in
    let uu____5752 =
      let uu____5753 =
        let uu____5754 = let uu____5759 = type_of ea  in as_arg uu____5759
           in
        [uu____5754]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____5753
       in
    mk_emb em un uu____5752 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____5832  ->
             Lam
               ((fun tas  ->
                   let uu____5864 =
                     let uu____5867 = FStar_List.hd tas  in
                     unembed ea cb uu____5867  in
                   match uu____5864 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____5869 = f a  in embed eb cb uu____5869
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____5882  ->
                     let uu____5885 = type_of eb  in as_arg uu____5885)],
                 Prims.int_one, FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____5945 =
                 let uu____5948 =
                   let uu____5949 =
                     let uu____5950 =
                       let uu____5955 = embed ea cb x  in as_arg uu____5955
                        in
                     [uu____5950]  in
                   cb.iapp lam1 uu____5949  in
                 unembed eb cb uu____5948  in
               match uu____5945 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____5969 =
        let uu____5970 = type_of ea  in
        let uu____5971 = let uu____5972 = type_of eb  in as_iarg uu____5972
           in
        make_arrow1 uu____5970 uu____5971  in
      mk_emb em un uu____5969 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____5990 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5990 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____5995 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5995 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____6000 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6000 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____6005 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6005 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____6010 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6010 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____6015 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6015 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____6020 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6020 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____6025 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6025 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____6030 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____6030 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____6039 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6040 =
          let uu____6041 =
            let uu____6046 =
              let uu____6047 = e_list e_string  in embed uu____6047 cb l  in
            as_arg uu____6046  in
          [uu____6041]  in
        mkFV uu____6039 [] uu____6040
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____6069 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6070 =
          let uu____6071 =
            let uu____6076 =
              let uu____6077 = e_list e_string  in embed uu____6077 cb l  in
            as_arg uu____6076  in
          [uu____6071]  in
        mkFV uu____6069 [] uu____6070
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____6099 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6100 =
          let uu____6101 =
            let uu____6106 =
              let uu____6107 = e_list e_string  in embed uu____6107 cb l  in
            as_arg uu____6106  in
          [uu____6101]  in
        mkFV uu____6099 [] uu____6100
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____6141,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____6157,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____6173,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____6189,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____6205,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____6221,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____6237,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____6253,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____6269,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____6285,(l,uu____6287)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____6306 =
          let uu____6312 = e_list e_string  in unembed uu____6312 cb l  in
        FStar_Util.bind_opt uu____6306
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6332  -> FStar_Pervasives_Native.Some _6332)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____6334,(l,uu____6336)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____6355 =
          let uu____6361 = e_list e_string  in unembed uu____6361 cb l  in
        FStar_Util.bind_opt uu____6355
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6381  -> FStar_Pervasives_Native.Some _6381)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____6383,(l,uu____6385)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____6404 =
          let uu____6410 = e_list e_string  in unembed uu____6410 cb l  in
        FStar_Util.bind_opt uu____6404
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6430  -> FStar_Pervasives_Native.Some _6430)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____6431 ->
        ((let uu____6433 =
            let uu____6439 =
              let uu____6441 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____6441
               in
            (FStar_Errors.Warning_NotEmbedded, uu____6439)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____6433);
         FStar_Pervasives_Native.None)
     in
  let uu____6445 =
    let uu____6446 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____6446 [] []  in
  let uu____6451 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____6445 uu____6451 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____6460  -> failwith "bogus_cbs translate")
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
      let uu____6537 =
        let uu____6546 = e_list e  in unembed uu____6546 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6537
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____6568  ->
    match uu____6568 with
    | (a,uu____6576) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____6591)::[]) when
             let uu____6608 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6608 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____6615 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____6658 = let uu____6665 = as_arg c  in [uu____6665]  in
      int_to_t2 uu____6658
  
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
          let uu____6719 = f a  in FStar_Pervasives_Native.Some uu____6719
      | uu____6720 -> FStar_Pervasives_Native.None
  
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
          let uu____6774 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____6774
      | uu____6775 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6819 = FStar_List.map as_a args  in lift_unary f uu____6819
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6874 = FStar_List.map as_a args  in
        lift_binary f uu____6874
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____6904 = f x  in embed e_int bogus_cbs uu____6904)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____6931 = f x y  in embed e_int bogus_cbs uu____6931)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____6957 = f x  in embed e_bool bogus_cbs uu____6957)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____6995 = f x y  in embed e_bool bogus_cbs uu____6995)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____7033 = f x y  in embed e_string bogus_cbs uu____7033)
  
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
                let uu____7138 =
                  let uu____7147 = as_a a  in
                  let uu____7150 = as_b b  in (uu____7147, uu____7150)  in
                (match uu____7138 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____7165 =
                       let uu____7166 = f a1 b1  in embed_c uu____7166  in
                     FStar_Pervasives_Native.Some uu____7165
                 | uu____7167 -> FStar_Pervasives_Native.None)
            | uu____7176 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____7185 = e_list e_char  in
    let uu____7192 = FStar_String.list_of_string s  in
    embed uu____7185 bogus_cbs uu____7192
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____7231 =
        let uu____7232 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____7232  in
      embed e_int bogus_cbs uu____7231
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7266 = arg_as_string a1  in
        (match uu____7266 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7275 = arg_as_list e_string a2  in
             (match uu____7275 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7293 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7293
              | uu____7295 -> FStar_Pervasives_Native.None)
         | uu____7301 -> FStar_Pervasives_Native.None)
    | uu____7305 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____7312 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____7312
  
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
      | (_typ,uu____7374)::(a1,uu____7376)::(a2,uu____7378)::[] ->
          let uu____7395 = eq_t a1 a2  in
          (match uu____7395 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____7404 -> FStar_Pervasives_Native.None)
      | uu____7405 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7420)::(_typ,uu____7422)::(a1,uu____7424)::(a2,uu____7426)::[]
        ->
        let uu____7447 = eq_t a1 a2  in
        (match uu____7447 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7450 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7450
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7453 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7453
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7456 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7471)::(_v,uu____7473)::(t1,uu____7475)::(t2,uu____7477)::
        (a1,uu____7479)::(a2,uu____7481)::[] ->
        let uu____7510 =
          let uu____7511 = eq_t t1 t2  in
          let uu____7512 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____7511 uu____7512  in
        (match uu____7510 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7515 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7515
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7518 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7518
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7521 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____7540 =
        let uu____7542 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____7542  in
      failwith uu____7540
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____7558)::[] ->
        let uu____7567 = unembed e_range bogus_cbs a1  in
        (match uu____7567 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7573 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____7573
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7574 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7610 = arg_as_list e_char a1  in
        (match uu____7610 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7626 = arg_as_string a2  in
             (match uu____7626 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____7639 =
                    let uu____7640 = e_list e_string  in
                    embed uu____7640 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7639
              | uu____7650 -> FStar_Pervasives_Native.None)
         | uu____7654 -> FStar_Pervasives_Native.None)
    | uu____7660 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7693 =
          let uu____7703 = arg_as_string a1  in
          let uu____7707 = arg_as_int a2  in (uu____7703, uu____7707)  in
        (match uu____7693 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___989_7731  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____7736 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7736) ()
              with | uu___988_7739 -> FStar_Pervasives_Native.None)
         | uu____7742 -> FStar_Pervasives_Native.None)
    | uu____7752 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7785 =
          let uu____7796 = arg_as_string a1  in
          let uu____7800 = arg_as_char a2  in (uu____7796, uu____7800)  in
        (match uu____7785 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1007_7829  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____7833 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7833) ()
              with | uu___1006_7835 -> FStar_Pervasives_Native.None)
         | uu____7838 -> FStar_Pervasives_Native.None)
    | uu____7849 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____7891 =
          let uu____7905 = arg_as_string a1  in
          let uu____7909 = arg_as_int a2  in
          let uu____7912 = arg_as_int a3  in
          (uu____7905, uu____7909, uu____7912)  in
        (match uu____7891 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1030_7945  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____7950 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7950) ()
              with | uu___1029_7953 -> FStar_Pervasives_Native.None)
         | uu____7956 -> FStar_Pervasives_Native.None)
    | uu____7970 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____8030 =
          let uu____8052 = arg_as_string fn  in
          let uu____8056 = arg_as_int from_line  in
          let uu____8059 = arg_as_int from_col  in
          let uu____8062 = arg_as_int to_line  in
          let uu____8065 = arg_as_int to_col  in
          (uu____8052, uu____8056, uu____8059, uu____8062, uu____8065)  in
        (match uu____8030 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8100 =
                 let uu____8101 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8103 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8101 uu____8103  in
               let uu____8105 =
                 let uu____8106 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8108 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8106 uu____8108  in
               FStar_Range.mk_range fn1 uu____8100 uu____8105  in
             let uu____8110 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8110
         | uu____8111 -> FStar_Pervasives_Native.None)
    | uu____8133 -> FStar_Pervasives_Native.None
  
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
                let uu____8223 = FStar_List.splitAt n_tvars args  in
                match uu____8223 with
                | (_tvar_args,rest_args) ->
                    let uu____8272 = FStar_List.hd rest_args  in
                    (match uu____8272 with
                     | (x,uu____8284) ->
                         let uu____8285 = unembed ea cb x  in
                         FStar_Util.map_opt uu____8285
                           (fun x1  ->
                              let uu____8291 = f x1  in
                              embed eb cb uu____8291))
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
                  let uu____8400 = FStar_List.splitAt n_tvars args  in
                  match uu____8400 with
                  | (_tvar_args,rest_args) ->
                      let uu____8449 = FStar_List.hd rest_args  in
                      (match uu____8449 with
                       | (x,uu____8461) ->
                           let uu____8462 =
                             let uu____8467 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____8467  in
                           (match uu____8462 with
                            | (y,uu____8485) ->
                                let uu____8486 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____8486
                                  (fun x1  ->
                                     let uu____8492 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____8492
                                       (fun y1  ->
                                          let uu____8498 =
                                            let uu____8499 = f x1 y1  in
                                            embed ec cb uu____8499  in
                                          FStar_Pervasives_Native.Some
                                            uu____8498))))
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
                    let uu____8627 = FStar_List.splitAt n_tvars args  in
                    match uu____8627 with
                    | (_tvar_args,rest_args) ->
                        let uu____8676 = FStar_List.hd rest_args  in
                        (match uu____8676 with
                         | (x,uu____8688) ->
                             let uu____8689 =
                               let uu____8694 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____8694  in
                             (match uu____8689 with
                              | (y,uu____8712) ->
                                  let uu____8713 =
                                    let uu____8718 =
                                      let uu____8725 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____8725  in
                                    FStar_List.hd uu____8718  in
                                  (match uu____8713 with
                                   | (z,uu____8747) ->
                                       let uu____8748 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____8748
                                         (fun x1  ->
                                            let uu____8754 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____8754
                                              (fun y1  ->
                                                 let uu____8760 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____8760
                                                   (fun z1  ->
                                                      let uu____8766 =
                                                        let uu____8767 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____8767
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____8766))))))
                     in
                  f_wrapped
  