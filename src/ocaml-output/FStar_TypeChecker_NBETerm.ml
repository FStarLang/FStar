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
  (unit -> residual_comp) FStar_Pervasives_Native.option) 
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
  | Reflect of (t * t) 
  | Quote of (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo) 
  | Lazy of
  ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                   FStar_Syntax_Syntax.emb_typ))
  FStar_Util.either * t FStar_Common.thunk) 
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
    match projectee with | Var _0 -> true | uu____559 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____595 -> false
  
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
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____814 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____877 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____952 -> false 
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____1013 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____1032 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1051 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1069 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____1101 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____1194 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1259 -> false
  
let (__proj__Reflect__item___0 : t -> (t * t)) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1294 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1339 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1436 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1569 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1612 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1649 -> false
  
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
    match projectee with | TOTAL  -> true | uu____1778 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____1789 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____1800 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____1811 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____1822 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____1833 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____1844 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____1855 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  -> match projectee with | CPS  -> true | uu____1866 -> false 
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____1878 -> false
  
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
  fun trm  -> match trm with | Accu uu____1954 -> true | uu____1966 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1976,uu____1977) -> false | uu____1991 -> true
  
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
  fun uu___0_2127  ->
    if uu___0_2127
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___1_2138  ->
    if uu___1_2138
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
      | (FStar_Syntax_Util.NotEqual ,uu____2154) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2155,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____2156) -> FStar_Syntax_Util.Unknown
      | (uu____2157,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____2174 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____2194),String (s2,uu____2196)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2209,uu____2210) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____2246,Lam uu____2247) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2336 = eq_atom a1 a2  in
          eq_and uu____2336 (fun uu____2338  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2377 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2377
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2393 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____2450  ->
                        match uu____2450 with
                        | ((a1,uu____2464),(a2,uu____2466)) ->
                            let uu____2475 = eq_t a1 a2  in
                            eq_inj acc uu____2475) FStar_Syntax_Util.Equal)
                uu____2393))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____2516 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2516
          then
            let uu____2519 =
              let uu____2520 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____2520  in
            eq_and uu____2519 (fun uu____2523  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____2530 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2530
      | (Univ u1,Univ u2) ->
          let uu____2534 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2534
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2581 =
            let uu____2582 =
              let uu____2583 = t11 ()  in
              FStar_Pervasives_Native.fst uu____2583  in
            let uu____2588 =
              let uu____2589 = t21 ()  in
              FStar_Pervasives_Native.fst uu____2589  in
            eq_t uu____2582 uu____2588  in
          eq_and uu____2581
            (fun uu____2597  ->
               let uu____2598 =
                 let uu____2599 = mkAccuVar x  in r1 uu____2599  in
               let uu____2600 =
                 let uu____2601 = mkAccuVar x  in r2 uu____2601  in
               eq_t uu____2598 uu____2600)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____2602,uu____2603) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____2608,uu____2609) -> FStar_Syntax_Util.Unknown

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
          let uu____2690 = eq_arg x y  in
          eq_and uu____2690 (fun uu____2692  -> eq_args xs ys)
      | (uu____2693,uu____2694) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2741) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2746 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2746
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____2775) ->
        let uu____2820 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2831 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____2820 uu____2831
    | Accu (a,l) ->
        let uu____2848 =
          let uu____2850 = atom_to_string a  in
          let uu____2852 =
            let uu____2854 =
              let uu____2856 =
                let uu____2858 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2858  in
              FStar_String.op_Hat uu____2856 ")"  in
            FStar_String.op_Hat ") (" uu____2854  in
          FStar_String.op_Hat uu____2850 uu____2852  in
        FStar_String.op_Hat "Accu (" uu____2848
    | Construct (fv,us,l) ->
        let uu____2896 =
          let uu____2898 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2900 =
            let uu____2902 =
              let uu____2904 =
                let uu____2906 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2906  in
              let uu____2912 =
                let uu____2914 =
                  let uu____2916 =
                    let uu____2918 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2918  in
                  FStar_String.op_Hat uu____2916 "]"  in
                FStar_String.op_Hat "] [" uu____2914  in
              FStar_String.op_Hat uu____2904 uu____2912  in
            FStar_String.op_Hat ") [" uu____2902  in
          FStar_String.op_Hat uu____2898 uu____2900  in
        FStar_String.op_Hat "Construct (" uu____2896
    | FV (fv,us,l) ->
        let uu____2957 =
          let uu____2959 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2961 =
            let uu____2963 =
              let uu____2965 =
                let uu____2967 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2967  in
              let uu____2973 =
                let uu____2975 =
                  let uu____2977 =
                    let uu____2979 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2979  in
                  FStar_String.op_Hat uu____2977 "]"  in
                FStar_String.op_Hat "] [" uu____2975  in
              FStar_String.op_Hat uu____2965 uu____2973  in
            FStar_String.op_Hat ") [" uu____2963  in
          FStar_String.op_Hat uu____2959 uu____2961  in
        FStar_String.op_Hat "FV (" uu____2957
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____3001 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____3001
    | Type_t u ->
        let uu____3005 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____3005
    | Arrow uu____3008 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____3054 = t ()  in FStar_Pervasives_Native.fst uu____3054
           in
        let uu____3059 =
          let uu____3061 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____3063 =
            let uu____3065 =
              let uu____3067 = t_to_string t1  in
              let uu____3069 =
                let uu____3071 =
                  let uu____3073 =
                    let uu____3075 =
                      let uu____3076 = mkAccuVar x1  in f uu____3076  in
                    t_to_string uu____3075  in
                  FStar_String.op_Hat uu____3073 "}"  in
                FStar_String.op_Hat "{" uu____3071  in
              FStar_String.op_Hat uu____3067 uu____3069  in
            FStar_String.op_Hat ":" uu____3065  in
          FStar_String.op_Hat uu____3061 uu____3063  in
        FStar_String.op_Hat "Refinement " uu____3059
    | Unknown  -> "Unknown"
    | Reflect (w,t) ->
        let uu____3084 =
          let uu____3086 = t_to_string w  in
          let uu____3088 =
            let uu____3090 =
              let uu____3092 = t_to_string t  in
              FStar_String.op_Hat uu____3092 ")"  in
            FStar_String.op_Hat ", " uu____3090  in
          FStar_String.op_Hat uu____3086 uu____3088  in
        FStar_String.op_Hat "Reflect (" uu____3084
    | Quote uu____3097 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____3104) ->
        let uu____3121 =
          let uu____3123 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____3123  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3121
    | Lazy (FStar_Util.Inr (uu____3125,et),uu____3127) ->
        let uu____3144 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3144
    | Rec
        (uu____3147,uu____3148,l,uu____3150,uu____3151,uu____3152,uu____3153)
        ->
        let uu____3198 =
          let uu____3200 =
            let uu____3202 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____3202  in
          FStar_String.op_Hat uu____3200 ")"  in
        FStar_String.op_Hat "Rec (" uu____3198

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____3213 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____3213
    | Match (t,uu____3217,uu____3218) ->
        let uu____3241 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____3241

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____3245 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____3245 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____3252 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____3252 (FStar_String.concat " ")

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
        let uu____3723 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____3723 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____3744 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____3744 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____3785  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____3800  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____3843 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____3843
         then
           let uu____3867 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____3867
         else ());
        (let uu____3872 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____3872
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li = let uu____3906 = FStar_Dyn.mkdyn x  in (uu____3906, et)
               in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____3934 'a .
    'Auu____3934 ->
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
              let uu____3985 = FStar_Common.force_thunk thunk1  in
              f uu____3985
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____4005 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____4005
              then
                let res =
                  let uu____4034 = FStar_Common.force_thunk thunk1  in
                  f uu____4034  in
                ((let uu____4036 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4036
                  then
                    let uu____4060 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____4062 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____4060
                      uu____4062
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____4071 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4071
                  then
                    let uu____4095 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____4095
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____4100 ->
              let aopt = f x  in
              ((let uu____4105 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____4105
                then
                  let uu____4129 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4129
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
  let uu____4197 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____4197 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____4231 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____4236 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4231 uu____4236 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____4277 -> FStar_Pervasives_Native.None  in
  let uu____4279 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____4284 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4279 uu____4284 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____4326 -> FStar_Pervasives_Native.None  in
  let uu____4328 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____4333 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____4328 uu____4333 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____4375)) -> FStar_Pervasives_Native.Some s1
    | uu____4379 -> FStar_Pervasives_Native.None  in
  let uu____4381 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____4386 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____4381 uu____4386 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____4421 -> FStar_Pervasives_Native.None  in
  let uu____4422 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____4427 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____4422 uu____4427 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____4448 =
        let uu____4456 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____4456, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4448  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____4481  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____4482 =
                 let uu____4483 =
                   let uu____4488 = type_of ea  in as_iarg uu____4488  in
                 [uu____4483]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4482
           | FStar_Pervasives_Native.Some x ->
               let uu____4498 =
                 let uu____4499 =
                   let uu____4504 = embed ea cb x  in as_arg uu____4504  in
                 let uu____4505 =
                   let uu____4512 =
                     let uu____4517 = type_of ea  in as_iarg uu____4517  in
                   [uu____4512]  in
                 uu____4499 :: uu____4505  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4498)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____4584)::uu____4585::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____4612 = unembed ea cb a  in
               FStar_Util.bind_opt uu____4612
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____4621 -> FStar_Pervasives_Native.None)
       in
    let uu____4624 =
      let uu____4625 =
        let uu____4626 = let uu____4631 = type_of ea  in as_arg uu____4631
           in
        [uu____4626]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____4625
       in
    mk_emb em un uu____4624 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4678 =
          let uu____4686 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____4686, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4678  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____4717  ->
             let uu____4718 =
               let uu____4719 =
                 let uu____4724 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____4724  in
               let uu____4725 =
                 let uu____4732 =
                   let uu____4737 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____4737  in
                 let uu____4738 =
                   let uu____4745 =
                     let uu____4750 = type_of eb  in as_iarg uu____4750  in
                   let uu____4751 =
                     let uu____4758 =
                       let uu____4763 = type_of ea  in as_iarg uu____4763  in
                     [uu____4758]  in
                   uu____4745 :: uu____4751  in
                 uu____4732 :: uu____4738  in
               uu____4719 :: uu____4725  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____4718)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____4831)::(a,uu____4833)::uu____4834::uu____4835::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____4874 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____4874
                   (fun a1  ->
                      let uu____4884 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____4884
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____4897 -> FStar_Pervasives_Native.None)
         in
      let uu____4902 =
        let uu____4903 =
          let uu____4904 = let uu____4909 = type_of eb  in as_arg uu____4909
             in
          let uu____4910 =
            let uu____4917 =
              let uu____4922 = type_of ea  in as_arg uu____4922  in
            [uu____4917]  in
          uu____4904 :: uu____4910  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4903
         in
      mk_emb em un uu____4902 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4975 =
          let uu____4983 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____4983, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4975  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____5015  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____5017 =
                   let uu____5018 =
                     let uu____5023 = embed ea cb a  in as_arg uu____5023  in
                   let uu____5024 =
                     let uu____5031 =
                       let uu____5036 = type_of eb  in as_iarg uu____5036  in
                     let uu____5037 =
                       let uu____5044 =
                         let uu____5049 = type_of ea  in as_iarg uu____5049
                          in
                       [uu____5044]  in
                     uu____5031 :: uu____5037  in
                   uu____5018 :: uu____5024  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5017
             | FStar_Util.Inr b ->
                 let uu____5067 =
                   let uu____5068 =
                     let uu____5073 = embed eb cb b  in as_arg uu____5073  in
                   let uu____5074 =
                     let uu____5081 =
                       let uu____5086 = type_of eb  in as_iarg uu____5086  in
                     let uu____5087 =
                       let uu____5094 =
                         let uu____5099 = type_of ea  in as_iarg uu____5099
                          in
                       [uu____5094]  in
                     uu____5081 :: uu____5087  in
                   uu____5068 :: uu____5074  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5067)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____5161)::uu____5162::uu____5163::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____5198 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____5198
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____5214)::uu____5215::uu____5216::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____5251 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____5251
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____5264 -> FStar_Pervasives_Native.None)
         in
      let uu____5269 =
        let uu____5270 =
          let uu____5271 = let uu____5276 = type_of eb  in as_arg uu____5276
             in
          let uu____5277 =
            let uu____5284 =
              let uu____5289 = type_of ea  in as_arg uu____5289  in
            [uu____5284]  in
          uu____5271 :: uu____5277  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5270
         in
      mk_emb em un uu____5269 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____5338 -> FStar_Pervasives_Native.None  in
  let uu____5339 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____5344 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____5339 uu____5344 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____5365 =
        let uu____5373 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____5373, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5365  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____5400  ->
           let typ = let uu____5402 = type_of ea  in as_iarg uu____5402  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____5423 =
               let uu____5424 = as_arg tl1  in
               let uu____5429 =
                 let uu____5436 =
                   let uu____5441 = embed ea cb hd1  in as_arg uu____5441  in
                 [uu____5436; typ]  in
               uu____5424 :: uu____5429  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____5423
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____5489,uu____5490) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____5510,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____5513,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5514))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5542 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5542
                 (fun hd2  ->
                    let uu____5550 = un cb tl1  in
                    FStar_Util.bind_opt uu____5550
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____5566,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5591 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5591
                 (fun hd2  ->
                    let uu____5599 = un cb tl1  in
                    FStar_Util.bind_opt uu____5599
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____5614 -> FStar_Pervasives_Native.None)
       in
    let uu____5617 =
      let uu____5618 =
        let uu____5619 = let uu____5624 = type_of ea  in as_arg uu____5624
           in
        [uu____5619]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____5618
       in
    mk_emb em un uu____5617 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____5697  ->
             Lam
               ((fun tas  ->
                   let uu____5727 =
                     let uu____5730 = FStar_List.hd tas  in
                     unembed ea cb uu____5730  in
                   match uu____5727 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____5732 = f a  in embed eb cb uu____5732
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____5745  ->
                     let uu____5748 = type_of eb  in as_arg uu____5748)],
                 Prims.int_one, FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____5806 =
                 let uu____5809 =
                   let uu____5810 =
                     let uu____5811 =
                       let uu____5816 = embed ea cb x  in as_arg uu____5816
                        in
                     [uu____5811]  in
                   cb.iapp lam1 uu____5810  in
                 unembed eb cb uu____5809  in
               match uu____5806 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____5830 =
        let uu____5831 = type_of ea  in
        let uu____5832 = let uu____5833 = type_of eb  in as_iarg uu____5833
           in
        make_arrow1 uu____5831 uu____5832  in
      mk_emb em un uu____5830 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____5851 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5851 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____5856 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5856 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____5861 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5861 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____5866 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5866 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____5871 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5871 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____5876 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5876 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____5881 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5881 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____5886 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5886 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____5891 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5891 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____5900 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5901 =
          let uu____5902 =
            let uu____5907 =
              let uu____5908 = e_list e_string  in embed uu____5908 cb l  in
            as_arg uu____5907  in
          [uu____5902]  in
        mkFV uu____5900 [] uu____5901
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____5930 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5931 =
          let uu____5932 =
            let uu____5937 =
              let uu____5938 = e_list e_string  in embed uu____5938 cb l  in
            as_arg uu____5937  in
          [uu____5932]  in
        mkFV uu____5930 [] uu____5931
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____5960 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____5961 =
          let uu____5962 =
            let uu____5967 =
              let uu____5968 = e_list e_string  in embed uu____5968 cb l  in
            as_arg uu____5967  in
          [uu____5962]  in
        mkFV uu____5960 [] uu____5961
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____6002,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____6018,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____6034,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____6050,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____6066,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____6082,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____6098,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____6114,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____6130,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____6146,(l,uu____6148)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____6167 =
          let uu____6173 = e_list e_string  in unembed uu____6173 cb l  in
        FStar_Util.bind_opt uu____6167
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6193  -> FStar_Pervasives_Native.Some _6193)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____6195,(l,uu____6197)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____6216 =
          let uu____6222 = e_list e_string  in unembed uu____6222 cb l  in
        FStar_Util.bind_opt uu____6216
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6242  -> FStar_Pervasives_Native.Some _6242)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____6244,(l,uu____6246)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____6265 =
          let uu____6271 = e_list e_string  in unembed uu____6271 cb l  in
        FStar_Util.bind_opt uu____6265
          (fun ss  ->
             FStar_All.pipe_left
               (fun _6291  -> FStar_Pervasives_Native.Some _6291)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____6292 ->
        ((let uu____6294 =
            let uu____6300 =
              let uu____6302 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____6302
               in
            (FStar_Errors.Warning_NotEmbedded, uu____6300)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____6294);
         FStar_Pervasives_Native.None)
     in
  let uu____6306 =
    let uu____6307 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____6307 [] []  in
  let uu____6312 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____6306 uu____6312 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____6321  -> failwith "bogus_cbs translate")
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
      let uu____6398 =
        let uu____6407 = e_list e  in unembed uu____6407 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6398
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____6429  ->
    match uu____6429 with
    | (a,uu____6437) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____6452)::[]) when
             let uu____6469 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6469 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____6476 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____6519 = let uu____6526 = as_arg c  in [uu____6526]  in
      int_to_t2 uu____6519
  
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
          let uu____6580 = f a  in FStar_Pervasives_Native.Some uu____6580
      | uu____6581 -> FStar_Pervasives_Native.None
  
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
          let uu____6635 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____6635
      | uu____6636 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6680 = FStar_List.map as_a args  in lift_unary f uu____6680
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6735 = FStar_List.map as_a args  in
        lift_binary f uu____6735
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____6765 = f x  in embed e_int bogus_cbs uu____6765)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____6792 = f x y  in embed e_int bogus_cbs uu____6792)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____6818 = f x  in embed e_bool bogus_cbs uu____6818)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____6856 = f x y  in embed e_bool bogus_cbs uu____6856)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____6894 = f x y  in embed e_string bogus_cbs uu____6894)
  
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
                let uu____6999 =
                  let uu____7008 = as_a a  in
                  let uu____7011 = as_b b  in (uu____7008, uu____7011)  in
                (match uu____6999 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____7026 =
                       let uu____7027 = f a1 b1  in embed_c uu____7027  in
                     FStar_Pervasives_Native.Some uu____7026
                 | uu____7028 -> FStar_Pervasives_Native.None)
            | uu____7037 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____7046 = e_list e_char  in
    let uu____7053 = FStar_String.list_of_string s  in
    embed uu____7046 bogus_cbs uu____7053
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____7092 =
        let uu____7093 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____7093  in
      embed e_int bogus_cbs uu____7092
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7127 = arg_as_string a1  in
        (match uu____7127 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7136 = arg_as_list e_string a2  in
             (match uu____7136 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7154 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7154
              | uu____7156 -> FStar_Pervasives_Native.None)
         | uu____7162 -> FStar_Pervasives_Native.None)
    | uu____7166 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____7173 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____7173
  
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
      | (_typ,uu____7235)::(a1,uu____7237)::(a2,uu____7239)::[] ->
          let uu____7256 = eq_t a1 a2  in
          (match uu____7256 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____7265 -> FStar_Pervasives_Native.None)
      | uu____7266 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7281)::(_typ,uu____7283)::(a1,uu____7285)::(a2,uu____7287)::[]
        ->
        let uu____7308 = eq_t a1 a2  in
        (match uu____7308 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7311 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7311
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7314 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7314
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7317 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7332)::(_v,uu____7334)::(t1,uu____7336)::(t2,uu____7338)::
        (a1,uu____7340)::(a2,uu____7342)::[] ->
        let uu____7371 =
          let uu____7372 = eq_t t1 t2  in
          let uu____7373 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____7372 uu____7373  in
        (match uu____7371 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7376 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7376
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7379 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7379
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7382 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____7401 =
        let uu____7403 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____7403  in
      failwith uu____7401
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____7419)::[] ->
        let uu____7428 = unembed e_range bogus_cbs a1  in
        (match uu____7428 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7434 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____7434
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7435 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7471 = arg_as_list e_char a1  in
        (match uu____7471 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7487 = arg_as_string a2  in
             (match uu____7487 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____7500 =
                    let uu____7501 = e_list e_string  in
                    embed uu____7501 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7500
              | uu____7511 -> FStar_Pervasives_Native.None)
         | uu____7515 -> FStar_Pervasives_Native.None)
    | uu____7521 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7554 =
          let uu____7564 = arg_as_string a1  in
          let uu____7568 = arg_as_int a2  in (uu____7564, uu____7568)  in
        (match uu____7554 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___983_7592  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____7597 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7597) ()
              with | uu___982_7600 -> FStar_Pervasives_Native.None)
         | uu____7603 -> FStar_Pervasives_Native.None)
    | uu____7613 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7646 =
          let uu____7657 = arg_as_string a1  in
          let uu____7661 = arg_as_char a2  in (uu____7657, uu____7661)  in
        (match uu____7646 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1001_7690  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____7694 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7694) ()
              with | uu___1000_7696 -> FStar_Pervasives_Native.None)
         | uu____7699 -> FStar_Pervasives_Native.None)
    | uu____7710 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____7752 =
          let uu____7766 = arg_as_string a1  in
          let uu____7770 = arg_as_int a2  in
          let uu____7773 = arg_as_int a3  in
          (uu____7766, uu____7770, uu____7773)  in
        (match uu____7752 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1024_7806  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____7811 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7811) ()
              with | uu___1023_7814 -> FStar_Pervasives_Native.None)
         | uu____7817 -> FStar_Pervasives_Native.None)
    | uu____7831 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7891 =
          let uu____7913 = arg_as_string fn  in
          let uu____7917 = arg_as_int from_line  in
          let uu____7920 = arg_as_int from_col  in
          let uu____7923 = arg_as_int to_line  in
          let uu____7926 = arg_as_int to_col  in
          (uu____7913, uu____7917, uu____7920, uu____7923, uu____7926)  in
        (match uu____7891 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____7961 =
                 let uu____7962 = FStar_BigInt.to_int_fs from_l  in
                 let uu____7964 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____7962 uu____7964  in
               let uu____7966 =
                 let uu____7967 = FStar_BigInt.to_int_fs to_l  in
                 let uu____7969 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____7967 uu____7969  in
               FStar_Range.mk_range fn1 uu____7961 uu____7966  in
             let uu____7971 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____7971
         | uu____7972 -> FStar_Pervasives_Native.None)
    | uu____7994 -> FStar_Pervasives_Native.None
  
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
                let uu____8084 = FStar_List.splitAt n_tvars args  in
                match uu____8084 with
                | (_tvar_args,rest_args) ->
                    let uu____8133 = FStar_List.hd rest_args  in
                    (match uu____8133 with
                     | (x,uu____8145) ->
                         let uu____8146 = unembed ea cb x  in
                         FStar_Util.map_opt uu____8146
                           (fun x1  ->
                              let uu____8152 = f x1  in
                              embed eb cb uu____8152))
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
                  let uu____8261 = FStar_List.splitAt n_tvars args  in
                  match uu____8261 with
                  | (_tvar_args,rest_args) ->
                      let uu____8310 = FStar_List.hd rest_args  in
                      (match uu____8310 with
                       | (x,uu____8322) ->
                           let uu____8323 =
                             let uu____8328 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____8328  in
                           (match uu____8323 with
                            | (y,uu____8346) ->
                                let uu____8347 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____8347
                                  (fun x1  ->
                                     let uu____8353 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____8353
                                       (fun y1  ->
                                          let uu____8359 =
                                            let uu____8360 = f x1 y1  in
                                            embed ec cb uu____8360  in
                                          FStar_Pervasives_Native.Some
                                            uu____8359))))
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
                    let uu____8488 = FStar_List.splitAt n_tvars args  in
                    match uu____8488 with
                    | (_tvar_args,rest_args) ->
                        let uu____8537 = FStar_List.hd rest_args  in
                        (match uu____8537 with
                         | (x,uu____8549) ->
                             let uu____8550 =
                               let uu____8555 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____8555  in
                             (match uu____8550 with
                              | (y,uu____8573) ->
                                  let uu____8574 =
                                    let uu____8579 =
                                      let uu____8586 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____8586  in
                                    FStar_List.hd uu____8579  in
                                  (match uu____8574 with
                                   | (z,uu____8608) ->
                                       let uu____8609 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____8609
                                         (fun x1  ->
                                            let uu____8615 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____8615
                                              (fun y1  ->
                                                 let uu____8621 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____8621
                                                   (fun z1  ->
                                                      let uu____8627 =
                                                        let uu____8628 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____8628
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____8627))))))
                     in
                  f_wrapped
  