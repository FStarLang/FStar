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
  | Rec of (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
  Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list *
  Prims.int * Prims.bool Prims.list *
  (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)) 
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
    match projectee with | Var _0 -> true | uu____557 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____593 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____695 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (t Prims.list -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____820 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____883 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____958 -> false 
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____1019 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____1038 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1057 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1075 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____1107 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____1200 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1261 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1284 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1329 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Thunk.t))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1426 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1559 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1602 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1639 -> false
  
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
    match projectee with | TOTAL  -> true | uu____1768 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____1779 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____1790 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____1801 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____1812 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____1823 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____1834 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____1845 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____1856 -> false 
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____1868 -> false
  
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
  fun trm  -> match trm with | Accu uu____1944 -> true | uu____1956 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1966,uu____1967) -> false | uu____1981 -> true
  
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
  fun uu___0_2117  ->
    if uu___0_2117
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2128  ->
    if uu___1_2128
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
      | (FStar_Syntax_Util.NotEqual ,uu____2144) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2145,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____2146) -> FStar_Syntax_Util.Unknown
      | (uu____2147,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____2164 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____2184),String (s2,uu____2186)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2199,uu____2200) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____2236,Lam uu____2237) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2330 = eq_atom a1 a2  in
          eq_and uu____2330 (fun uu____2332  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2371 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2371
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2387 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____2444  ->
                        match uu____2444 with
                        | ((a1,uu____2458),(a2,uu____2460)) ->
                            let uu____2469 = eq_t a1 a2  in
                            eq_inj acc uu____2469) FStar_Syntax_Util.Equal)
                uu____2387))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____2510 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2510
          then
            let uu____2513 =
              let uu____2514 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____2514  in
            eq_and uu____2513 (fun uu____2517  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____2524 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2524
      | (Univ u1,Univ u2) ->
          let uu____2528 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2528
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2575 =
            let uu____2576 =
              let uu____2577 = t11 ()  in
              FStar_Pervasives_Native.fst uu____2577  in
            let uu____2582 =
              let uu____2583 = t21 ()  in
              FStar_Pervasives_Native.fst uu____2583  in
            eq_t uu____2576 uu____2582  in
          eq_and uu____2575
            (fun uu____2591  ->
               let uu____2592 =
                 let uu____2593 = mkAccuVar x  in r1 uu____2593  in
               let uu____2594 =
                 let uu____2595 = mkAccuVar x  in r2 uu____2595  in
               eq_t uu____2592 uu____2594)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____2596,uu____2597) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____2602,uu____2603) -> FStar_Syntax_Util.Unknown

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
          let uu____2684 = eq_arg x y  in
          eq_and uu____2684 (fun uu____2686  -> eq_args xs ys)
      | (uu____2687,uu____2688) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2735) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2740 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2740
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____2759) ->
        let uu____2808 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2819 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____2808 uu____2819
    | Accu (a,l) ->
        let uu____2836 =
          let uu____2838 = atom_to_string a  in
          let uu____2840 =
            let uu____2842 =
              let uu____2844 =
                let uu____2846 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2846  in
              FStar_String.op_Hat uu____2844 ")"  in
            FStar_String.op_Hat ") (" uu____2842  in
          FStar_String.op_Hat uu____2838 uu____2840  in
        FStar_String.op_Hat "Accu (" uu____2836
    | Construct (fv,us,l) ->
        let uu____2884 =
          let uu____2886 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2888 =
            let uu____2890 =
              let uu____2892 =
                let uu____2894 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2894  in
              let uu____2900 =
                let uu____2902 =
                  let uu____2904 =
                    let uu____2906 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2906  in
                  FStar_String.op_Hat uu____2904 "]"  in
                FStar_String.op_Hat "] [" uu____2902  in
              FStar_String.op_Hat uu____2892 uu____2900  in
            FStar_String.op_Hat ") [" uu____2890  in
          FStar_String.op_Hat uu____2886 uu____2888  in
        FStar_String.op_Hat "Construct (" uu____2884
    | FV (fv,us,l) ->
        let uu____2945 =
          let uu____2947 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2949 =
            let uu____2951 =
              let uu____2953 =
                let uu____2955 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2955  in
              let uu____2961 =
                let uu____2963 =
                  let uu____2965 =
                    let uu____2967 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2967  in
                  FStar_String.op_Hat uu____2965 "]"  in
                FStar_String.op_Hat "] [" uu____2963  in
              FStar_String.op_Hat uu____2953 uu____2961  in
            FStar_String.op_Hat ") [" uu____2951  in
          FStar_String.op_Hat uu____2947 uu____2949  in
        FStar_String.op_Hat "FV (" uu____2945
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2989 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____2989
    | Type_t u ->
        let uu____2993 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____2993
    | Arrow uu____2996 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____3042 = t ()  in FStar_Pervasives_Native.fst uu____3042
           in
        let uu____3047 =
          let uu____3049 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____3051 =
            let uu____3053 =
              let uu____3055 = t_to_string t1  in
              let uu____3057 =
                let uu____3059 =
                  let uu____3061 =
                    let uu____3063 =
                      let uu____3064 = mkAccuVar x1  in f uu____3064  in
                    t_to_string uu____3063  in
                  FStar_String.op_Hat uu____3061 "}"  in
                FStar_String.op_Hat "{" uu____3059  in
              FStar_String.op_Hat uu____3055 uu____3057  in
            FStar_String.op_Hat ":" uu____3053  in
          FStar_String.op_Hat uu____3049 uu____3051  in
        FStar_String.op_Hat "Refinement " uu____3047
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____3071 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____3071
    | Quote uu____3074 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____3081) ->
        let uu____3098 =
          let uu____3100 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____3100  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3098
    | Lazy (FStar_Util.Inr (uu____3102,et),uu____3104) ->
        let uu____3121 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3121
    | Rec
        (uu____3124,uu____3125,l,uu____3127,uu____3128,uu____3129,uu____3130)
        ->
        let uu____3175 =
          let uu____3177 =
            let uu____3179 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____3179  in
          FStar_String.op_Hat uu____3177 ")"  in
        FStar_String.op_Hat "Rec (" uu____3175

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____3190 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____3190
    | Match (t,uu____3194,uu____3195) ->
        let uu____3218 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____3218

let (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____3228 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____3228 t_to_string
  
let (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____3241 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____3241 (FStar_String.concat " ")
  
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
        let uu____3712 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____3712 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____3733 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____3733 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____3774  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____3789  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____3832 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____3832
         then
           let uu____3856 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____3856
         else ());
        (let uu____3861 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____3861
         then f ()
         else
           (let thunk1 = FStar_Thunk.mk f  in
            let li = let uu____3895 = FStar_Dyn.mkdyn x  in (uu____3895, et)
               in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____3923 'a .
    'Auu____3923 ->
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
              let uu____3974 = FStar_Thunk.force thunk1  in f uu____3974
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____3994 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____3994
              then
                let res =
                  let uu____4023 = FStar_Thunk.force thunk1  in f uu____4023
                   in
                ((let uu____4025 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4025
                  then
                    let uu____4049 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____4051 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____4049
                      uu____4051
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____4060 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4060
                  then
                    let uu____4084 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____4084
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____4089 ->
              let aopt = f x  in
              ((let uu____4094 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____4094
                then
                  let uu____4118 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4118
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
  let uu____4186 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____4186 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____4220 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____4225 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4220 uu____4225 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____4266 -> FStar_Pervasives_Native.None  in
  let uu____4268 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____4273 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4268 uu____4273 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____4315 -> FStar_Pervasives_Native.None  in
  let uu____4317 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____4322 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____4317 uu____4322 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____4364)) -> FStar_Pervasives_Native.Some s1
    | uu____4368 -> FStar_Pervasives_Native.None  in
  let uu____4370 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____4375 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____4370 uu____4375 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____4410 -> FStar_Pervasives_Native.None  in
  let uu____4411 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____4416 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____4411 uu____4416 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____4437 =
        let uu____4445 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____4445, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4437  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____4470  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____4471 =
                 let uu____4472 =
                   let uu____4477 = type_of ea  in as_iarg uu____4477  in
                 [uu____4472]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4471
           | FStar_Pervasives_Native.Some x ->
               let uu____4487 =
                 let uu____4488 =
                   let uu____4493 = embed ea cb x  in as_arg uu____4493  in
                 let uu____4494 =
                   let uu____4501 =
                     let uu____4506 = type_of ea  in as_iarg uu____4506  in
                   [uu____4501]  in
                 uu____4488 :: uu____4494  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4487)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____4573)::uu____4574::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____4601 = unembed ea cb a  in
               FStar_Util.bind_opt uu____4601
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____4610 -> FStar_Pervasives_Native.None)
       in
    let uu____4613 =
      let uu____4614 =
        let uu____4615 = let uu____4620 = type_of ea  in as_arg uu____4620
           in
        [uu____4615]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____4614
       in
    mk_emb em un uu____4613 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4667 =
          let uu____4675 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____4675, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4667  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____4706  ->
             let uu____4707 =
               let uu____4708 =
                 let uu____4713 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____4713  in
               let uu____4714 =
                 let uu____4721 =
                   let uu____4726 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____4726  in
                 let uu____4727 =
                   let uu____4734 =
                     let uu____4739 = type_of eb  in as_iarg uu____4739  in
                   let uu____4740 =
                     let uu____4747 =
                       let uu____4752 = type_of ea  in as_iarg uu____4752  in
                     [uu____4747]  in
                   uu____4734 :: uu____4740  in
                 uu____4721 :: uu____4727  in
               uu____4708 :: uu____4714  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____4707)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____4820)::(a,uu____4822)::uu____4823::uu____4824::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____4863 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____4863
                   (fun a1  ->
                      let uu____4873 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____4873
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____4886 -> FStar_Pervasives_Native.None)
         in
      let uu____4891 =
        let uu____4892 =
          let uu____4893 = let uu____4898 = type_of eb  in as_arg uu____4898
             in
          let uu____4899 =
            let uu____4906 =
              let uu____4911 = type_of ea  in as_arg uu____4911  in
            [uu____4906]  in
          uu____4893 :: uu____4899  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4892
         in
      mk_emb em un uu____4891 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4964 =
          let uu____4972 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____4972, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4964  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____5004  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____5006 =
                   let uu____5007 =
                     let uu____5012 = embed ea cb a  in as_arg uu____5012  in
                   let uu____5013 =
                     let uu____5020 =
                       let uu____5025 = type_of eb  in as_iarg uu____5025  in
                     let uu____5026 =
                       let uu____5033 =
                         let uu____5038 = type_of ea  in as_iarg uu____5038
                          in
                       [uu____5033]  in
                     uu____5020 :: uu____5026  in
                   uu____5007 :: uu____5013  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5006
             | FStar_Util.Inr b ->
                 let uu____5056 =
                   let uu____5057 =
                     let uu____5062 = embed eb cb b  in as_arg uu____5062  in
                   let uu____5063 =
                     let uu____5070 =
                       let uu____5075 = type_of eb  in as_iarg uu____5075  in
                     let uu____5076 =
                       let uu____5083 =
                         let uu____5088 = type_of ea  in as_iarg uu____5088
                          in
                       [uu____5083]  in
                     uu____5070 :: uu____5076  in
                   uu____5057 :: uu____5063  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5056)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____5150)::uu____5151::uu____5152::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____5187 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____5187
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____5203)::uu____5204::uu____5205::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____5240 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____5240
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____5253 -> FStar_Pervasives_Native.None)
         in
      let uu____5258 =
        let uu____5259 =
          let uu____5260 = let uu____5265 = type_of eb  in as_arg uu____5265
             in
          let uu____5266 =
            let uu____5273 =
              let uu____5278 = type_of ea  in as_arg uu____5278  in
            [uu____5273]  in
          uu____5260 :: uu____5266  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5259
         in
      mk_emb em un uu____5258 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____5327 -> FStar_Pervasives_Native.None  in
  let uu____5328 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____5333 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____5328 uu____5333 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____5354 =
        let uu____5362 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____5362, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5354  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____5389  ->
           let typ = let uu____5391 = type_of ea  in as_iarg uu____5391  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____5412 =
               let uu____5413 = as_arg tl1  in
               let uu____5418 =
                 let uu____5425 =
                   let uu____5430 = embed ea cb hd1  in as_arg uu____5430  in
                 [uu____5425; typ]  in
               uu____5413 :: uu____5418  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____5412
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____5478,uu____5479) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____5499,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____5502,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5503))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5531 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5531
                 (fun hd2  ->
                    let uu____5539 = un cb tl1  in
                    FStar_Util.bind_opt uu____5539
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____5555,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5580 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5580
                 (fun hd2  ->
                    let uu____5588 = un cb tl1  in
                    FStar_Util.bind_opt uu____5588
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____5603 -> FStar_Pervasives_Native.None)
       in
    let uu____5606 =
      let uu____5607 =
        let uu____5608 = let uu____5613 = type_of ea  in as_arg uu____5613
           in
        [uu____5608]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____5607
       in
    mk_emb em un uu____5606 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____5686  ->
             Lam
               ((fun tas  ->
                   let uu____5718 =
                     let uu____5721 = FStar_List.hd tas  in
                     unembed ea cb uu____5721  in
                   match uu____5718 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____5723 = f a  in embed eb cb uu____5723
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____5736  ->
                     let uu____5739 = type_of eb  in as_arg uu____5739)],
                 Prims.int_one, FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____5799 =
                 let uu____5802 =
                   let uu____5803 =
                     let uu____5804 =
                       let uu____5809 = embed ea cb x  in as_arg uu____5809
                        in
                     [uu____5804]  in
                   cb.iapp lam1 uu____5803  in
                 unembed eb cb uu____5802  in
               match uu____5799 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____5823 =
        let uu____5824 = type_of ea  in
        let uu____5825 = let uu____5826 = type_of eb  in as_iarg uu____5826
           in
        make_arrow1 uu____5824 uu____5825  in
      mk_emb em un uu____5823 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____5844 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5844 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____5849 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5849 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____5854 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5854 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____5859 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5859 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____5864 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5864 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____5869 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5869 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____5874 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5874 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____5879 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5879 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____5884 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5884 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____5893 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5894 =
          let uu____5895 =
            let uu____5900 =
              let uu____5901 = e_list e_string  in embed uu____5901 cb l  in
            as_arg uu____5900  in
          [uu____5895]  in
        mkFV uu____5893 [] uu____5894
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____5923 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5924 =
          let uu____5925 =
            let uu____5930 =
              let uu____5931 = e_list e_string  in embed uu____5931 cb l  in
            as_arg uu____5930  in
          [uu____5925]  in
        mkFV uu____5923 [] uu____5924
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____5953 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5954 =
          let uu____5955 =
            let uu____5960 =
              let uu____5961 = e_list e_string  in embed uu____5961 cb l  in
            as_arg uu____5960  in
          [uu____5955]  in
        mkFV uu____5953 [] uu____5954
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____5995,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____6011,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____6027,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____6043,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____6059,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____6075,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____6091,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____6107,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____6123,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____6139,(l,uu____6141)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____6160 =
          let uu____6166 = e_list e_string  in unembed uu____6166 cb l  in
        FStar_Util.bind_opt uu____6160
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6186  -> FStar_Pervasives_Native.Some _6186)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____6188,(l,uu____6190)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____6209 =
          let uu____6215 = e_list e_string  in unembed uu____6215 cb l  in
        FStar_Util.bind_opt uu____6209
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6235  -> FStar_Pervasives_Native.Some _6235)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____6237,(l,uu____6239)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____6258 =
          let uu____6264 = e_list e_string  in unembed uu____6264 cb l  in
        FStar_Util.bind_opt uu____6258
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6284  -> FStar_Pervasives_Native.Some _6284)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____6285 ->
        ((let uu____6287 =
            let uu____6293 =
              let uu____6295 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____6295
               in
            (FStar_Errors.Warning_NotEmbedded, uu____6293)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____6287);
         FStar_Pervasives_Native.None)
     in
  let uu____6299 =
    let uu____6300 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____6300 [] []  in
  let uu____6305 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____6299 uu____6305 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____6314  -> failwith "bogus_cbs translate")
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
      let uu____6391 =
        let uu____6400 = e_list e  in unembed uu____6400 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6391
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____6422  ->
    match uu____6422 with
    | (a,uu____6430) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____6445)::[]) when
             let uu____6462 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6462 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____6469 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____6512 = let uu____6519 = as_arg c  in [uu____6519]  in
      int_to_t2 uu____6512
  
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
          let uu____6573 = f a  in FStar_Pervasives_Native.Some uu____6573
      | uu____6574 -> FStar_Pervasives_Native.None
  
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
          let uu____6628 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____6628
      | uu____6629 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6673 = FStar_List.map as_a args  in lift_unary f uu____6673
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6728 = FStar_List.map as_a args  in
        lift_binary f uu____6728
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____6758 = f x  in embed e_int bogus_cbs uu____6758)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____6785 = f x y  in embed e_int bogus_cbs uu____6785)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____6811 = f x  in embed e_bool bogus_cbs uu____6811)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____6849 = f x y  in embed e_bool bogus_cbs uu____6849)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____6887 = f x y  in embed e_string bogus_cbs uu____6887)
  
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
                let uu____6992 =
                  let uu____7001 = as_a a  in
                  let uu____7004 = as_b b  in (uu____7001, uu____7004)  in
                (match uu____6992 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____7019 =
                       let uu____7020 = f a1 b1  in embed_c uu____7020  in
                     FStar_Pervasives_Native.Some uu____7019
                 | uu____7021 -> FStar_Pervasives_Native.None)
            | uu____7030 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____7039 = e_list e_char  in
    let uu____7046 = FStar_String.list_of_string s  in
    embed uu____7039 bogus_cbs uu____7046
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____7085 =
        let uu____7086 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____7086  in
      embed e_int bogus_cbs uu____7085
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7120 = arg_as_string a1  in
        (match uu____7120 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7129 = arg_as_list e_string a2  in
             (match uu____7129 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7147 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7147
              | uu____7149 -> FStar_Pervasives_Native.None)
         | uu____7155 -> FStar_Pervasives_Native.None)
    | uu____7159 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____7166 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____7166
  
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
      | (_typ,uu____7228)::(a1,uu____7230)::(a2,uu____7232)::[] ->
          let uu____7249 = eq_t a1 a2  in
          (match uu____7249 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____7258 -> FStar_Pervasives_Native.None)
      | uu____7259 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7274)::(_typ,uu____7276)::(a1,uu____7278)::(a2,uu____7280)::[]
        ->
        let uu____7301 = eq_t a1 a2  in
        (match uu____7301 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7304 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7304
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7307 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7307
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7310 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7325)::(_v,uu____7327)::(t1,uu____7329)::(t2,uu____7331)::
        (a1,uu____7333)::(a2,uu____7335)::[] ->
        let uu____7364 =
          let uu____7365 = eq_t t1 t2  in
          let uu____7366 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____7365 uu____7366  in
        (match uu____7364 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7369 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7369
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7372 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7372
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7375 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____7394 =
        let uu____7396 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____7396  in
      failwith uu____7394
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____7412)::[] ->
        let uu____7421 = unembed e_range bogus_cbs a1  in
        (match uu____7421 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7427 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____7427
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7428 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7464 = arg_as_list e_char a1  in
        (match uu____7464 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7480 = arg_as_string a2  in
             (match uu____7480 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____7493 =
                    let uu____7494 = e_list e_string  in
                    embed uu____7494 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7493
              | uu____7504 -> FStar_Pervasives_Native.None)
         | uu____7508 -> FStar_Pervasives_Native.None)
    | uu____7514 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7547 =
          let uu____7557 = arg_as_string a1  in
          let uu____7561 = arg_as_int a2  in (uu____7557, uu____7561)  in
        (match uu____7547 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___981_7585  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____7590 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7590) ()
              with | uu___980_7593 -> FStar_Pervasives_Native.None)
         | uu____7596 -> FStar_Pervasives_Native.None)
    | uu____7606 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7639 =
          let uu____7650 = arg_as_string a1  in
          let uu____7654 = arg_as_char a2  in (uu____7650, uu____7654)  in
        (match uu____7639 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___999_7683  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____7687 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7687) ()
              with | uu___998_7689 -> FStar_Pervasives_Native.None)
         | uu____7692 -> FStar_Pervasives_Native.None)
    | uu____7703 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____7745 =
          let uu____7759 = arg_as_string a1  in
          let uu____7763 = arg_as_int a2  in
          let uu____7766 = arg_as_int a3  in
          (uu____7759, uu____7763, uu____7766)  in
        (match uu____7745 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1022_7799  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____7804 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7804) ()
              with | uu___1021_7807 -> FStar_Pervasives_Native.None)
         | uu____7810 -> FStar_Pervasives_Native.None)
    | uu____7824 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7884 =
          let uu____7906 = arg_as_string fn  in
          let uu____7910 = arg_as_int from_line  in
          let uu____7913 = arg_as_int from_col  in
          let uu____7916 = arg_as_int to_line  in
          let uu____7919 = arg_as_int to_col  in
          (uu____7906, uu____7910, uu____7913, uu____7916, uu____7919)  in
        (match uu____7884 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7954 =
                 let uu____7955 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7957 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7955 uu____7957  in
               let uu____7959 =
                 let uu____7960 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7962 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7960 uu____7962  in
               FStar_Range.mk_range fn1 uu____7954 uu____7959  in
             let uu____7964 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____7964
         | uu____7965 -> FStar_Pervasives_Native.None)
    | uu____7987 -> FStar_Pervasives_Native.None
  
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
                let uu____8077 = FStar_List.splitAt n_tvars args  in
                match uu____8077 with
                | (_tvar_args,rest_args) ->
                    let uu____8126 = FStar_List.hd rest_args  in
                    (match uu____8126 with
                     | (x,uu____8138) ->
                         let uu____8139 = unembed ea cb x  in
                         FStar_Util.map_opt uu____8139
                           (fun x1  ->
                              let uu____8145 = f x1  in
                              embed eb cb uu____8145))
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
                  let uu____8254 = FStar_List.splitAt n_tvars args  in
                  match uu____8254 with
                  | (_tvar_args,rest_args) ->
                      let uu____8303 = FStar_List.hd rest_args  in
                      (match uu____8303 with
                       | (x,uu____8315) ->
                           let uu____8316 =
                             let uu____8321 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____8321  in
                           (match uu____8316 with
                            | (y,uu____8339) ->
                                let uu____8340 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____8340
                                  (fun x1  ->
                                     let uu____8346 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____8346
                                       (fun y1  ->
                                          let uu____8352 =
                                            let uu____8353 = f x1 y1  in
                                            embed ec cb uu____8353  in
                                          FStar_Pervasives_Native.Some
                                            uu____8352))))
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
                    let uu____8481 = FStar_List.splitAt n_tvars args  in
                    match uu____8481 with
                    | (_tvar_args,rest_args) ->
                        let uu____8530 = FStar_List.hd rest_args  in
                        (match uu____8530 with
                         | (x,uu____8542) ->
                             let uu____8543 =
                               let uu____8548 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____8548  in
                             (match uu____8543 with
                              | (y,uu____8566) ->
                                  let uu____8567 =
                                    let uu____8572 =
                                      let uu____8579 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____8579  in
                                    FStar_List.hd uu____8572  in
                                  (match uu____8567 with
                                   | (z,uu____8601) ->
                                       let uu____8602 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____8602
                                         (fun x1  ->
                                            let uu____8608 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____8608
                                              (fun y1  ->
                                                 let uu____8614 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____8614
                                                   (fun z1  ->
                                                      let uu____8620 =
                                                        let uu____8621 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____8621
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____8620))))))
                     in
                  f_wrapped
  