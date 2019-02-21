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
  fun projectee  -> match projectee with | Unit  -> true | uu____44 -> false 
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____57 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Int _0 -> true | uu____80 -> false 
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____105 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____141 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____164 -> false
  
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
  | Reflect of t 
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
    match projectee with | Var _0 -> true | uu____547 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____584 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____685 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____805 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____869 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____945 -> false 
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____1007 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____1027 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____1047 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____1066 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____1098 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____1192 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____1254 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1278 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1324 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1422 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1556 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1600 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1638 -> false
  
let (__proj__Comp__item___0 : comp -> comp_typ) =
  fun projectee  -> match projectee with | Comp _0 -> _0 
let (__proj__Mkcomp_typ__item__comp_univs :
  comp_typ -> FStar_Syntax_Syntax.universes) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags = flags1;_}
        -> comp_univs
  
let (__proj__Mkcomp_typ__item__effect_name : comp_typ -> FStar_Ident.lident)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags = flags1;_}
        -> effect_name
  
let (__proj__Mkcomp_typ__item__result_typ : comp_typ -> t) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags = flags1;_}
        -> result_typ
  
let (__proj__Mkcomp_typ__item__effect_args :
  comp_typ -> (t * FStar_Syntax_Syntax.aqual) Prims.list) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags = flags1;_}
        -> effect_args
  
let (__proj__Mkcomp_typ__item__flags : comp_typ -> cflag Prims.list) =
  fun projectee  ->
    match projectee with
    | { comp_univs; effect_name; result_typ; effect_args; flags = flags1;_}
        -> flags1
  
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
  fun trm  -> match trm with | Accu uu____1945 -> true | uu____1957 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1967,uu____1968) -> false | uu____1982 -> true
  
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
  fun uu___1_2118  ->
    if uu___1_2118
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___2_2129  ->
    if uu___2_2129
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
      | (FStar_Syntax_Util.NotEqual ,uu____2145) ->
          FStar_Syntax_Util.NotEqual
      | (uu____2146,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____2147) -> FStar_Syntax_Util.Unknown
      | (uu____2148,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____2165 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____2185),String (s2,uu____2187)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____2200,uu____2201) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____2237,Lam uu____2238) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____2327 = eq_atom a1 a2  in
          eq_and uu____2327 (fun uu____2329  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____2368 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2368
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____2384 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____2441  ->
                        match uu____2441 with
                        | ((a1,uu____2455),(a2,uu____2457)) ->
                            let uu____2466 = eq_t a1 a2  in
                            eq_inj acc uu____2466) FStar_Syntax_Util.Equal)
                uu____2384))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____2507 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____2507
          then
            let uu____2510 =
              let uu____2511 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____2511  in
            eq_and uu____2510 (fun uu____2514  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____2521 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2521
      | (Univ u1,Univ u2) ->
          let uu____2525 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____2525
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____2572 =
            let uu____2573 =
              let uu____2574 = t11 ()  in
              FStar_Pervasives_Native.fst uu____2574  in
            let uu____2579 =
              let uu____2580 = t21 ()  in
              FStar_Pervasives_Native.fst uu____2580  in
            eq_t uu____2573 uu____2579  in
          eq_and uu____2572
            (fun uu____2588  ->
               let uu____2589 =
                 let uu____2590 = mkAccuVar x  in r1 uu____2590  in
               let uu____2591 =
                 let uu____2592 = mkAccuVar x  in r2 uu____2592  in
               eq_t uu____2589 uu____2591)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____2593,uu____2594) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____2599,uu____2600) -> FStar_Syntax_Util.Unknown

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
          let uu____2681 = eq_arg x y  in
          eq_and uu____2681 (fun uu____2683  -> eq_args xs ys)
      | (uu____2684,uu____2685) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2732) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2737 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2737
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____2766) ->
        let uu____2811 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2822 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____2811 uu____2822
    | Accu (a,l) ->
        let uu____2839 =
          let uu____2841 = atom_to_string a  in
          let uu____2843 =
            let uu____2845 =
              let uu____2847 =
                let uu____2849 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2849  in
              FStar_String.op_Hat uu____2847 ")"  in
            FStar_String.op_Hat ") (" uu____2845  in
          FStar_String.op_Hat uu____2841 uu____2843  in
        FStar_String.op_Hat "Accu (" uu____2839
    | Construct (fv,us,l) ->
        let uu____2887 =
          let uu____2889 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2891 =
            let uu____2893 =
              let uu____2895 =
                let uu____2897 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2897  in
              let uu____2903 =
                let uu____2905 =
                  let uu____2907 =
                    let uu____2909 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2909  in
                  FStar_String.op_Hat uu____2907 "]"  in
                FStar_String.op_Hat "] [" uu____2905  in
              FStar_String.op_Hat uu____2895 uu____2903  in
            FStar_String.op_Hat ") [" uu____2893  in
          FStar_String.op_Hat uu____2889 uu____2891  in
        FStar_String.op_Hat "Construct (" uu____2887
    | FV (fv,us,l) ->
        let uu____2948 =
          let uu____2950 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2952 =
            let uu____2954 =
              let uu____2956 =
                let uu____2958 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2958  in
              let uu____2964 =
                let uu____2966 =
                  let uu____2968 =
                    let uu____2970 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2970  in
                  FStar_String.op_Hat uu____2968 "]"  in
                FStar_String.op_Hat "] [" uu____2966  in
              FStar_String.op_Hat uu____2956 uu____2964  in
            FStar_String.op_Hat ") [" uu____2954  in
          FStar_String.op_Hat uu____2950 uu____2952  in
        FStar_String.op_Hat "FV (" uu____2948
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2992 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____2992
    | Type_t u ->
        let uu____2996 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____2996
    | Arrow uu____2999 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____3045 = t ()  in FStar_Pervasives_Native.fst uu____3045
           in
        let uu____3050 =
          let uu____3052 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____3054 =
            let uu____3056 =
              let uu____3058 = t_to_string t1  in
              let uu____3060 =
                let uu____3062 =
                  let uu____3064 =
                    let uu____3066 =
                      let uu____3067 = mkAccuVar x1  in f uu____3067  in
                    t_to_string uu____3066  in
                  FStar_String.op_Hat uu____3064 "}"  in
                FStar_String.op_Hat "{" uu____3062  in
              FStar_String.op_Hat uu____3058 uu____3060  in
            FStar_String.op_Hat ":" uu____3056  in
          FStar_String.op_Hat uu____3052 uu____3054  in
        FStar_String.op_Hat "Refinement " uu____3050
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____3074 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____3074
    | Quote uu____3077 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____3084) ->
        let uu____3101 =
          let uu____3103 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____3103  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____3101
    | Lazy (FStar_Util.Inr (uu____3105,et),uu____3107) ->
        let uu____3124 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____3124
    | Rec
        (uu____3127,uu____3128,l,uu____3130,uu____3131,uu____3132,uu____3133)
        ->
        let uu____3178 =
          let uu____3180 =
            let uu____3182 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____3182  in
          FStar_String.op_Hat uu____3180 ")"  in
        FStar_String.op_Hat "Rec (" uu____3178

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____3193 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____3193
    | Match (t,uu____3197,uu____3198) ->
        let uu____3221 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____3221

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____3225 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____3225 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____3232 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____3232 (FStar_String.concat " ")

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
        let uu____3703 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____3703 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____3724 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____3724 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____3765  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____3780  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____3823 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____3823
         then
           let uu____3847 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____3847
         else ());
        (let uu____3852 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____3852
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li = let uu____3886 = FStar_Dyn.mkdyn x  in (uu____3886, et)
               in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____3954 'a .
    'Auu____3954 ->
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
              let uu____4005 = FStar_Common.force_thunk thunk1  in
              f uu____4005
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____4065 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____4065
              then
                let res =
                  let uu____4094 = FStar_Common.force_thunk thunk1  in
                  f uu____4094  in
                ((let uu____4136 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4136
                  then
                    let uu____4160 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____4162 = FStar_Syntax_Print.emb_typ_to_string et'
                       in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____4160
                      uu____4162
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____4171 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____4171
                  then
                    let uu____4195 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n" uu____4195
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____4200 ->
              let aopt = f x  in
              ((let uu____4205 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____4205
                then
                  let uu____4229 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n" uu____4229
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
  let uu____4297 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____4297 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____4331 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____4336 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4331 uu____4336 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____4377 -> FStar_Pervasives_Native.None  in
  let uu____4379 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____4384 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____4379 uu____4384 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____4426 -> FStar_Pervasives_Native.None  in
  let uu____4428 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____4433 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____4428 uu____4433 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____4475)) -> FStar_Pervasives_Native.Some s1
    | uu____4479 -> FStar_Pervasives_Native.None  in
  let uu____4481 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____4486 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____4481 uu____4486 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____4521 -> FStar_Pervasives_Native.None  in
  let uu____4522 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____4527 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____4522 uu____4527 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____4548 =
        let uu____4556 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____4556, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____4548  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____4581  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____4582 =
                 let uu____4583 =
                   let uu____4588 = type_of ea  in as_iarg uu____4588  in
                 [uu____4583]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4582
           | FStar_Pervasives_Native.Some x ->
               let uu____4598 =
                 let uu____4599 =
                   let uu____4604 = embed ea cb x  in as_arg uu____4604  in
                 let uu____4605 =
                   let uu____4612 =
                     let uu____4617 = type_of ea  in as_iarg uu____4617  in
                   [uu____4612]  in
                 uu____4599 :: uu____4605  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____4598)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____4684)::uu____4685::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____4712 = unembed ea cb a  in
               FStar_Util.bind_opt uu____4712
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____4721 -> FStar_Pervasives_Native.None)
       in
    let uu____4724 =
      let uu____4725 =
        let uu____4726 = let uu____4731 = type_of ea  in as_arg uu____4731
           in
        [uu____4726]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____4725
       in
    mk_emb em un uu____4724 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____4778 =
          let uu____4786 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____4786, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____4778  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____4817  ->
             let uu____4818 =
               let uu____4819 =
                 let uu____4824 = embed eb cb (FStar_Pervasives_Native.snd x)
                    in
                 as_arg uu____4824  in
               let uu____4825 =
                 let uu____4832 =
                   let uu____4837 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____4837  in
                 let uu____4838 =
                   let uu____4845 =
                     let uu____4850 = type_of eb  in as_iarg uu____4850  in
                   let uu____4851 =
                     let uu____4858 =
                       let uu____4863 = type_of ea  in as_iarg uu____4863  in
                     [uu____4858]  in
                   uu____4845 :: uu____4851  in
                 uu____4832 :: uu____4838  in
               uu____4819 :: uu____4825  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____4818)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____4931)::(a,uu____4933)::uu____4934::uu____4935::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____4974 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____4974
                   (fun a1  ->
                      let uu____4984 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____4984
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____4997 -> FStar_Pervasives_Native.None)
         in
      let uu____5002 =
        let uu____5003 =
          let uu____5004 = let uu____5009 = type_of eb  in as_arg uu____5009
             in
          let uu____5010 =
            let uu____5017 =
              let uu____5022 = type_of ea  in as_arg uu____5022  in
            [uu____5017]  in
          uu____5004 :: uu____5010  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5003
         in
      mk_emb em un uu____5002 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____5075 =
          let uu____5083 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____5083, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____5075  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____5115  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____5117 =
                   let uu____5118 =
                     let uu____5123 = embed ea cb a  in as_arg uu____5123  in
                   let uu____5124 =
                     let uu____5131 =
                       let uu____5136 = type_of eb  in as_iarg uu____5136  in
                     let uu____5137 =
                       let uu____5144 =
                         let uu____5149 = type_of ea  in as_iarg uu____5149
                          in
                       [uu____5144]  in
                     uu____5131 :: uu____5137  in
                   uu____5118 :: uu____5124  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5117
             | FStar_Util.Inr b ->
                 let uu____5167 =
                   let uu____5168 =
                     let uu____5173 = embed eb cb b  in as_arg uu____5173  in
                   let uu____5174 =
                     let uu____5181 =
                       let uu____5186 = type_of eb  in as_iarg uu____5186  in
                     let uu____5187 =
                       let uu____5194 =
                         let uu____5199 = type_of ea  in as_iarg uu____5199
                          in
                       [uu____5194]  in
                     uu____5181 :: uu____5187  in
                   uu____5168 :: uu____5174  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____5167)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____5261)::uu____5262::uu____5263::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____5298 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____5298
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____5314)::uu____5315::uu____5316::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____5351 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____5351
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____5364 -> FStar_Pervasives_Native.None)
         in
      let uu____5369 =
        let uu____5370 =
          let uu____5371 = let uu____5376 = type_of eb  in as_arg uu____5376
             in
          let uu____5377 =
            let uu____5384 =
              let uu____5389 = type_of ea  in as_arg uu____5389  in
            [uu____5384]  in
          uu____5371 :: uu____5377  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____5370
         in
      mk_emb em un uu____5369 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____5438 -> FStar_Pervasives_Native.None  in
  let uu____5439 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____5444 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____5439 uu____5444 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____5465 =
        let uu____5473 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____5473, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____5465  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____5500  ->
           let typ = let uu____5502 = type_of ea  in as_iarg uu____5502  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____5523 =
               let uu____5524 = as_arg tl1  in
               let uu____5529 =
                 let uu____5536 =
                   let uu____5541 = embed ea cb hd1  in as_arg uu____5541  in
                 [uu____5536; typ]  in
               uu____5524 :: uu____5529  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____5523
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____5589,uu____5590) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____5610,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____5613,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____5614))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5642 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5642
                 (fun hd2  ->
                    let uu____5650 = un cb tl1  in
                    FStar_Util.bind_opt uu____5650
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____5666,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____5691 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____5691
                 (fun hd2  ->
                    let uu____5699 = un cb tl1  in
                    FStar_Util.bind_opt uu____5699
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____5714 -> FStar_Pervasives_Native.None)
       in
    let uu____5717 =
      let uu____5718 =
        let uu____5719 = let uu____5724 = type_of ea  in as_arg uu____5724
           in
        [uu____5719]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____5718
       in
    mk_emb em un uu____5717 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____5797  ->
             Lam
               ((fun tas  ->
                   let uu____5827 =
                     let uu____5830 = FStar_List.hd tas  in
                     unembed ea cb uu____5830  in
                   match uu____5827 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____5832 = f a  in embed eb cb uu____5832
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____5845  ->
                     let uu____5848 = type_of eb  in as_arg uu____5848)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____5906 =
                 let uu____5909 =
                   let uu____5910 =
                     let uu____5911 =
                       let uu____5916 = embed ea cb x  in as_arg uu____5916
                        in
                     [uu____5911]  in
                   cb.iapp lam1 uu____5910  in
                 unembed eb cb uu____5909  in
               match uu____5906 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____5930 =
        let uu____5931 = type_of ea  in
        let uu____5932 = let uu____5933 = type_of eb  in as_iarg uu____5933
           in
        make_arrow1 uu____5931 uu____5932  in
      mk_emb em un uu____5930 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____5951 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5951 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____5956 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5956 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____5961 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5961 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____5966 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5966 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____5971 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5971 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____5976 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5976 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____5981 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5981 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____5986 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5986 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____5991 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____5991 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____6000 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6001 =
          let uu____6002 =
            let uu____6007 =
              let uu____6008 = e_list e_string  in embed uu____6008 cb l  in
            as_arg uu____6007  in
          [uu____6002]  in
        mkFV uu____6000 [] uu____6001
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____6030 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6031 =
          let uu____6032 =
            let uu____6037 =
              let uu____6038 = e_list e_string  in embed uu____6038 cb l  in
            as_arg uu____6037  in
          [uu____6032]  in
        mkFV uu____6030 [] uu____6031
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____6060 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____6061 =
          let uu____6062 =
            let uu____6067 =
              let uu____6068 = e_list e_string  in embed uu____6068 cb l  in
            as_arg uu____6067  in
          [uu____6062]  in
        mkFV uu____6060 [] uu____6061
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____6102,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____6118,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____6134,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____6150,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____6166,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____6182,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____6198,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____6214,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____6230,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____6246,(l,uu____6248)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____6267 =
          let uu____6273 = e_list e_string  in unembed uu____6273 cb l  in
        FStar_Util.bind_opt uu____6267
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_1  -> FStar_Pervasives_Native.Some _0_1)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____6294,(l,uu____6296)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____6315 =
          let uu____6321 = e_list e_string  in unembed uu____6321 cb l  in
        FStar_Util.bind_opt uu____6315
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_2  -> FStar_Pervasives_Native.Some _0_2)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____6342,(l,uu____6344)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____6363 =
          let uu____6369 = e_list e_string  in unembed uu____6369 cb l  in
        FStar_Util.bind_opt uu____6363
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_3  -> FStar_Pervasives_Native.Some _0_3)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____6389 ->
        ((let uu____6391 =
            let uu____6397 =
              let uu____6399 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____6399
               in
            (FStar_Errors.Warning_NotEmbedded, uu____6397)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____6391);
         FStar_Pervasives_Native.None)
     in
  let uu____6403 =
    let uu____6404 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____6404 [] []  in
  let uu____6409 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____6403 uu____6409 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____6418  -> failwith "bogus_cbs translate")
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
      let uu____6495 =
        let uu____6504 = e_list e  in unembed uu____6504 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____6495
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____6526  ->
    match uu____6526 with
    | (a,uu____6534) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____6549)::[]) when
             let uu____6566 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____6566 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____6573 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____6616 = let uu____6623 = as_arg c  in [uu____6623]  in
      int_to_t2 uu____6616
  
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
          let uu____6677 = f a  in FStar_Pervasives_Native.Some uu____6677
      | uu____6678 -> FStar_Pervasives_Native.None
  
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
          let uu____6732 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____6732
      | uu____6733 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6777 = FStar_List.map as_a args  in lift_unary f uu____6777
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____6832 = FStar_List.map as_a args  in
        lift_binary f uu____6832
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____6862 = f x  in embed e_int bogus_cbs uu____6862)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____6889 = f x y  in embed e_int bogus_cbs uu____6889)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____6915 = f x  in embed e_bool bogus_cbs uu____6915)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____6953 = f x y  in embed e_bool bogus_cbs uu____6953)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____6991 = f x y  in embed e_string bogus_cbs uu____6991)
  
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
                let uu____7096 =
                  let uu____7105 = as_a a  in
                  let uu____7108 = as_b b  in (uu____7105, uu____7108)  in
                (match uu____7096 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____7123 =
                       let uu____7124 = f a1 b1  in embed_c uu____7124  in
                     FStar_Pervasives_Native.Some uu____7123
                 | uu____7125 -> FStar_Pervasives_Native.None)
            | uu____7134 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____7143 = e_list e_char  in
    let uu____7150 = FStar_String.list_of_string s  in
    embed uu____7143 bogus_cbs uu____7150
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____7189 =
        let uu____7190 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____7190  in
      embed e_int bogus_cbs uu____7189
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7224 = arg_as_string a1  in
        (match uu____7224 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7233 = arg_as_list e_string a2  in
             (match uu____7233 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____7251 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7251
              | uu____7253 -> FStar_Pervasives_Native.None)
         | uu____7259 -> FStar_Pervasives_Native.None)
    | uu____7263 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____7270 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____7270
  
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
      | (_typ,uu____7332)::(a1,uu____7334)::(a2,uu____7336)::[] ->
          let uu____7353 = eq_t a1 a2  in
          (match uu____7353 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____7362 -> FStar_Pervasives_Native.None)
      | uu____7363 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7378)::(_typ,uu____7380)::(a1,uu____7382)::(a2,uu____7384)::[]
        ->
        let uu____7405 = eq_t a1 a2  in
        (match uu____7405 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7408 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7408
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7411 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7411
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7414 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____7429)::(_v,uu____7431)::(t1,uu____7433)::(t2,uu____7435)::
        (a1,uu____7437)::(a2,uu____7439)::[] ->
        let uu____7468 =
          let uu____7469 = eq_t t1 t2  in
          let uu____7470 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____7469 uu____7470  in
        (match uu____7468 with
         | FStar_Syntax_Util.Equal  ->
             let uu____7473 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____7473
         | FStar_Syntax_Util.NotEqual  ->
             let uu____7476 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____7476
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____7479 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____7498 =
        let uu____7500 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____7500  in
      failwith uu____7498
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____7516)::[] ->
        let uu____7525 = unembed e_range bogus_cbs a1  in
        (match uu____7525 with
         | FStar_Pervasives_Native.Some r ->
             let uu____7531 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____7531
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____7532 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7568 = arg_as_list e_char a1  in
        (match uu____7568 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____7584 = arg_as_string a2  in
             (match uu____7584 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____7597 =
                    let uu____7598 = e_list e_string  in
                    embed uu____7598 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____7597
              | uu____7608 -> FStar_Pervasives_Native.None)
         | uu____7612 -> FStar_Pervasives_Native.None)
    | uu____7618 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7651 =
          let uu____7661 = arg_as_string a1  in
          let uu____7665 = arg_as_int a2  in (uu____7661, uu____7665)  in
        (match uu____7651 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___4_7689  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____7694 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7694) ()
              with | uu___3_7697 -> FStar_Pervasives_Native.None)
         | uu____7700 -> FStar_Pervasives_Native.None)
    | uu____7710 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____7743 =
          let uu____7754 = arg_as_string a1  in
          let uu____7758 = arg_as_char a2  in (uu____7754, uu____7758)  in
        (match uu____7743 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___6_7787  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____7791 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7791) ()
              with | uu___5_7793 -> FStar_Pervasives_Native.None)
         | uu____7796 -> FStar_Pervasives_Native.None)
    | uu____7807 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____7849 =
          let uu____7863 = arg_as_string a1  in
          let uu____7867 = arg_as_int a2  in
          let uu____7870 = arg_as_int a3  in
          (uu____7863, uu____7867, uu____7870)  in
        (match uu____7849 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___8_7903  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____7908 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____7908) ()
              with | uu___7_7911 -> FStar_Pervasives_Native.None)
         | uu____7914 -> FStar_Pervasives_Native.None)
    | uu____7928 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____7988 =
          let uu____8010 = arg_as_string fn  in
          let uu____8014 = arg_as_int from_line  in
          let uu____8017 = arg_as_int from_col  in
          let uu____8020 = arg_as_int to_line  in
          let uu____8023 = arg_as_int to_col  in
          (uu____8010, uu____8014, uu____8017, uu____8020, uu____8023)  in
        (match uu____7988 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____8058 =
                 let uu____8059 = FStar_BigInt.to_int_fs from_l  in
                 let uu____8061 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____8059 uu____8061  in
               let uu____8063 =
                 let uu____8064 = FStar_BigInt.to_int_fs to_l  in
                 let uu____8066 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____8064 uu____8066  in
               FStar_Range.mk_range fn1 uu____8058 uu____8063  in
             let uu____8068 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____8068
         | uu____8069 -> FStar_Pervasives_Native.None)
    | uu____8091 -> FStar_Pervasives_Native.None
  
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
                let uu____8181 = FStar_List.splitAt n_tvars args  in
                match uu____8181 with
                | (_tvar_args,rest_args) ->
                    let uu____8230 = FStar_List.hd rest_args  in
                    (match uu____8230 with
                     | (x,uu____8242) ->
                         let uu____8243 = unembed ea cb x  in
                         FStar_Util.map_opt uu____8243
                           (fun x1  ->
                              let uu____8249 = f x1  in
                              embed eb cb uu____8249))
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
                  let uu____8358 = FStar_List.splitAt n_tvars args  in
                  match uu____8358 with
                  | (_tvar_args,rest_args) ->
                      let uu____8407 = FStar_List.hd rest_args  in
                      (match uu____8407 with
                       | (x,uu____8419) ->
                           let uu____8420 =
                             let uu____8425 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____8425  in
                           (match uu____8420 with
                            | (y,uu____8443) ->
                                let uu____8444 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____8444
                                  (fun x1  ->
                                     let uu____8450 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____8450
                                       (fun y1  ->
                                          let uu____8456 =
                                            let uu____8457 = f x1 y1  in
                                            embed ec cb uu____8457  in
                                          FStar_Pervasives_Native.Some
                                            uu____8456))))
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
                    let uu____8585 = FStar_List.splitAt n_tvars args  in
                    match uu____8585 with
                    | (_tvar_args,rest_args) ->
                        let uu____8634 = FStar_List.hd rest_args  in
                        (match uu____8634 with
                         | (x,uu____8646) ->
                             let uu____8647 =
                               let uu____8652 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____8652  in
                             (match uu____8647 with
                              | (y,uu____8670) ->
                                  let uu____8671 =
                                    let uu____8676 =
                                      let uu____8683 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____8683  in
                                    FStar_List.hd uu____8676  in
                                  (match uu____8671 with
                                   | (z,uu____8705) ->
                                       let uu____8706 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____8706
                                         (fun x1  ->
                                            let uu____8712 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____8712
                                              (fun y1  ->
                                                 let uu____8718 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____8718
                                                   (fun z1  ->
                                                      let uu____8724 =
                                                        let uu____8725 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____8725
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____8724))))))
                     in
                  f_wrapped
  