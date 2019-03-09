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
  fun projectee  ->
    match projectee with | Unit  -> true | uu____55912 -> false
  
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____55925 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____55947 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____55971 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____56006 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____56028 -> false
  
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
    match projectee with | Var _0 -> true | uu____56410 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____56446 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____56546 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____56665 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____56728 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____56803 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____56864 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____56883 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____56902 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____56920 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____56952 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____57045 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____57106 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____57129 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____57174 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____57271 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____57404 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____57447 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____57484 -> false
  
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
    match projectee with | TOTAL  -> true | uu____57613 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____57624 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____57635 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____57646 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____57657 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____57668 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____57679 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____57690 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CPS  -> true | uu____57701 -> false
  
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____57713 -> false
  
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
    match trm with | Accu uu____57789 -> true | uu____57801 -> false
  
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with
    | Accu (uu____57811,uu____57812) -> false
    | uu____57826 -> true
  
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
  fun uu___516_57962  ->
    if uu___516_57962
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___517_57973  ->
    if uu___517_57973
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
      | (FStar_Syntax_Util.NotEqual ,uu____57989) ->
          FStar_Syntax_Util.NotEqual
      | (uu____57990,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____57991) -> FStar_Syntax_Util.Unknown
      | (uu____57992,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____58009 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____58029),String (s2,uu____58031)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____58044,uu____58045) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____58081,Lam uu____58082) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____58171 = eq_atom a1 a2  in
          eq_and uu____58171 (fun uu____58173  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____58212 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____58212
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____58228 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____58285  ->
                        match uu____58285 with
                        | ((a1,uu____58299),(a2,uu____58301)) ->
                            let uu____58310 = eq_t a1 a2  in
                            eq_inj acc uu____58310) FStar_Syntax_Util.Equal)
                uu____58228))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____58351 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____58351
          then
            let uu____58354 =
              let uu____58355 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____58355  in
            eq_and uu____58354 (fun uu____58358  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____58365 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____58365
      | (Univ u1,Univ u2) ->
          let uu____58369 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____58369
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____58416 =
            let uu____58417 =
              let uu____58418 = t11 ()  in
              FStar_Pervasives_Native.fst uu____58418  in
            let uu____58423 =
              let uu____58424 = t21 ()  in
              FStar_Pervasives_Native.fst uu____58424  in
            eq_t uu____58417 uu____58423  in
          eq_and uu____58416
            (fun uu____58432  ->
               let uu____58433 =
                 let uu____58434 = mkAccuVar x  in r1 uu____58434  in
               let uu____58435 =
                 let uu____58436 = mkAccuVar x  in r2 uu____58436  in
               eq_t uu____58433 uu____58435)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____58437,uu____58438) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____58443,uu____58444) -> FStar_Syntax_Util.Unknown

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
          let uu____58525 = eq_arg x y  in
          eq_and uu____58525 (fun uu____58527  -> eq_args xs ys)
      | (uu____58528,uu____58529) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____58576) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____58581 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____58581
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____58610) ->
        let uu____58655 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____58666 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____58655 uu____58666
    | Accu (a,l) ->
        let uu____58683 =
          let uu____58685 = atom_to_string a  in
          let uu____58687 =
            let uu____58689 =
              let uu____58691 =
                let uu____58693 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____58693  in
              FStar_String.op_Hat uu____58691 ")"  in
            FStar_String.op_Hat ") (" uu____58689  in
          FStar_String.op_Hat uu____58685 uu____58687  in
        FStar_String.op_Hat "Accu (" uu____58683
    | Construct (fv,us,l) ->
        let uu____58731 =
          let uu____58733 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____58735 =
            let uu____58737 =
              let uu____58739 =
                let uu____58741 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____58741  in
              let uu____58747 =
                let uu____58749 =
                  let uu____58751 =
                    let uu____58753 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____58753  in
                  FStar_String.op_Hat uu____58751 "]"  in
                FStar_String.op_Hat "] [" uu____58749  in
              FStar_String.op_Hat uu____58739 uu____58747  in
            FStar_String.op_Hat ") [" uu____58737  in
          FStar_String.op_Hat uu____58733 uu____58735  in
        FStar_String.op_Hat "Construct (" uu____58731
    | FV (fv,us,l) ->
        let uu____58792 =
          let uu____58794 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____58796 =
            let uu____58798 =
              let uu____58800 =
                let uu____58802 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____58802  in
              let uu____58808 =
                let uu____58810 =
                  let uu____58812 =
                    let uu____58814 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____58814  in
                  FStar_String.op_Hat uu____58812 "]"  in
                FStar_String.op_Hat "] [" uu____58810  in
              FStar_String.op_Hat uu____58800 uu____58808  in
            FStar_String.op_Hat ") [" uu____58798  in
          FStar_String.op_Hat uu____58794 uu____58796  in
        FStar_String.op_Hat "FV (" uu____58792
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____58836 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____58836
    | Type_t u ->
        let uu____58840 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____58840
    | Arrow uu____58843 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____58889 = t ()  in FStar_Pervasives_Native.fst uu____58889
           in
        let uu____58894 =
          let uu____58896 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____58898 =
            let uu____58900 =
              let uu____58902 = t_to_string t1  in
              let uu____58904 =
                let uu____58906 =
                  let uu____58908 =
                    let uu____58910 =
                      let uu____58911 = mkAccuVar x1  in f uu____58911  in
                    t_to_string uu____58910  in
                  FStar_String.op_Hat uu____58908 "}"  in
                FStar_String.op_Hat "{" uu____58906  in
              FStar_String.op_Hat uu____58902 uu____58904  in
            FStar_String.op_Hat ":" uu____58900  in
          FStar_String.op_Hat uu____58896 uu____58898  in
        FStar_String.op_Hat "Refinement " uu____58894
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____58918 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____58918
    | Quote uu____58921 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____58928) ->
        let uu____58945 =
          let uu____58947 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____58947  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____58945
    | Lazy (FStar_Util.Inr (uu____58949,et),uu____58951) ->
        let uu____58968 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____58968
    | Rec
        (uu____58971,uu____58972,l,uu____58974,uu____58975,uu____58976,uu____58977)
        ->
        let uu____59022 =
          let uu____59024 =
            let uu____59026 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____59026  in
          FStar_String.op_Hat uu____59024 ")"  in
        FStar_String.op_Hat "Rec (" uu____59022

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____59037 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____59037
    | Match (t,uu____59041,uu____59042) ->
        let uu____59065 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____59065

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____59069 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____59069 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____59076 =
      FStar_All.pipe_right args (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____59076 (FStar_String.concat " ")

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
        let uu____59547 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____59547 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____59568 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____59568 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____59609  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____59624  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____59667 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____59667
         then
           let uu____59691 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____59691
         else ());
        (let uu____59696 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____59696
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li =
              let uu____59730 = FStar_Dyn.mkdyn x  in (uu____59730, et)  in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____59758 'a .
    'Auu____59758 ->
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
              let uu____59809 = FStar_Common.force_thunk thunk1  in
              f uu____59809
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____59829 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____59829
              then
                let res =
                  let uu____59858 = FStar_Common.force_thunk thunk1  in
                  f uu____59858  in
                ((let uu____59860 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____59860
                  then
                    let uu____59884 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____59886 =
                      FStar_Syntax_Print.emb_typ_to_string et'  in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____59884
                      uu____59886
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____59895 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____59895
                  then
                    let uu____59919 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n"
                      uu____59919
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____59924 ->
              let aopt = f x  in
              ((let uu____59929 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____59929
                then
                  let uu____59953 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n"
                    uu____59953
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
  let uu____60021 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____60021 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____60055 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____60060 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____60055 uu____60060 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____60101 -> FStar_Pervasives_Native.None  in
  let uu____60103 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____60108 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____60103 uu____60108 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____60150 -> FStar_Pervasives_Native.None  in
  let uu____60152 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____60157 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____60152 uu____60157 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____60199)) -> FStar_Pervasives_Native.Some s1
    | uu____60203 -> FStar_Pervasives_Native.None  in
  let uu____60205 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____60210 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____60205 uu____60210 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____60245 -> FStar_Pervasives_Native.None  in
  let uu____60246 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____60251 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____60246 uu____60251 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____60272 =
        let uu____60280 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____60280, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____60272  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____60305  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____60306 =
                 let uu____60307 =
                   let uu____60312 = type_of ea  in as_iarg uu____60312  in
                 [uu____60307]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____60306
           | FStar_Pervasives_Native.Some x ->
               let uu____60322 =
                 let uu____60323 =
                   let uu____60328 = embed ea cb x  in as_arg uu____60328  in
                 let uu____60329 =
                   let uu____60336 =
                     let uu____60341 = type_of ea  in as_iarg uu____60341  in
                   [uu____60336]  in
                 uu____60323 :: uu____60329  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____60322)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____60408)::uu____60409::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____60436 = unembed ea cb a  in
               FStar_Util.bind_opt uu____60436
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____60445 -> FStar_Pervasives_Native.None)
       in
    let uu____60448 =
      let uu____60449 =
        let uu____60450 = let uu____60455 = type_of ea  in as_arg uu____60455
           in
        [uu____60450]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____60449
       in
    mk_emb em un uu____60448 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____60502 =
          let uu____60510 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____60510, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60502  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____60541  ->
             let uu____60542 =
               let uu____60543 =
                 let uu____60548 =
                   embed eb cb (FStar_Pervasives_Native.snd x)  in
                 as_arg uu____60548  in
               let uu____60549 =
                 let uu____60556 =
                   let uu____60561 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____60561  in
                 let uu____60562 =
                   let uu____60569 =
                     let uu____60574 = type_of eb  in as_iarg uu____60574  in
                   let uu____60575 =
                     let uu____60582 =
                       let uu____60587 = type_of ea  in as_iarg uu____60587
                        in
                     [uu____60582]  in
                   uu____60569 :: uu____60575  in
                 uu____60556 :: uu____60562  in
               uu____60543 :: uu____60549  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____60542)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____60655)::(a,uu____60657)::uu____60658::uu____60659::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____60698 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____60698
                   (fun a1  ->
                      let uu____60708 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____60708
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____60721 -> FStar_Pervasives_Native.None)
         in
      let uu____60726 =
        let uu____60727 =
          let uu____60728 =
            let uu____60733 = type_of eb  in as_arg uu____60733  in
          let uu____60734 =
            let uu____60741 =
              let uu____60746 = type_of ea  in as_arg uu____60746  in
            [uu____60741]  in
          uu____60728 :: uu____60734  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____60727
         in
      mk_emb em un uu____60726 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____60799 =
          let uu____60807 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____60807, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60799  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____60839  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____60841 =
                   let uu____60842 =
                     let uu____60847 = embed ea cb a  in as_arg uu____60847
                      in
                   let uu____60848 =
                     let uu____60855 =
                       let uu____60860 = type_of eb  in as_iarg uu____60860
                        in
                     let uu____60861 =
                       let uu____60868 =
                         let uu____60873 = type_of ea  in as_iarg uu____60873
                          in
                       [uu____60868]  in
                     uu____60855 :: uu____60861  in
                   uu____60842 :: uu____60848  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____60841
             | FStar_Util.Inr b ->
                 let uu____60891 =
                   let uu____60892 =
                     let uu____60897 = embed eb cb b  in as_arg uu____60897
                      in
                   let uu____60898 =
                     let uu____60905 =
                       let uu____60910 = type_of eb  in as_iarg uu____60910
                        in
                     let uu____60911 =
                       let uu____60918 =
                         let uu____60923 = type_of ea  in as_iarg uu____60923
                          in
                       [uu____60918]  in
                     uu____60905 :: uu____60911  in
                   uu____60892 :: uu____60898  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____60891)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____60985)::uu____60986::uu____60987::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____61022 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____61022
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____61038)::uu____61039::uu____61040::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____61075 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____61075
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____61088 -> FStar_Pervasives_Native.None)
         in
      let uu____61093 =
        let uu____61094 =
          let uu____61095 =
            let uu____61100 = type_of eb  in as_arg uu____61100  in
          let uu____61101 =
            let uu____61108 =
              let uu____61113 = type_of ea  in as_arg uu____61113  in
            [uu____61108]  in
          uu____61095 :: uu____61101  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____61094
         in
      mk_emb em un uu____61093 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____61162 -> FStar_Pervasives_Native.None  in
  let uu____61163 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____61168 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____61163 uu____61168 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____61189 =
        let uu____61197 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____61197, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____61189  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____61224  ->
           let typ = let uu____61226 = type_of ea  in as_iarg uu____61226  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____61247 =
               let uu____61248 = as_arg tl1  in
               let uu____61253 =
                 let uu____61260 =
                   let uu____61265 = embed ea cb hd1  in as_arg uu____61265
                    in
                 [uu____61260; typ]  in
               uu____61248 :: uu____61253  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____61247
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____61313,uu____61314) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____61334,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____61337,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____61338))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____61366 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____61366
                 (fun hd2  ->
                    let uu____61374 = un cb tl1  in
                    FStar_Util.bind_opt uu____61374
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____61390,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____61415 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____61415
                 (fun hd2  ->
                    let uu____61423 = un cb tl1  in
                    FStar_Util.bind_opt uu____61423
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____61438 -> FStar_Pervasives_Native.None)
       in
    let uu____61441 =
      let uu____61442 =
        let uu____61443 = let uu____61448 = type_of ea  in as_arg uu____61448
           in
        [uu____61443]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____61442
       in
    mk_emb em un uu____61441 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____61521  ->
             Lam
               ((fun tas  ->
                   let uu____61551 =
                     let uu____61554 = FStar_List.hd tas  in
                     unembed ea cb uu____61554  in
                   match uu____61551 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____61556 = f a  in embed eb cb uu____61556
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____61569  ->
                     let uu____61572 = type_of eb  in as_arg uu____61572)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____61630 =
                 let uu____61633 =
                   let uu____61634 =
                     let uu____61635 =
                       let uu____61640 = embed ea cb x  in as_arg uu____61640
                        in
                     [uu____61635]  in
                   cb.iapp lam1 uu____61634  in
                 unembed eb cb uu____61633  in
               match uu____61630 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____61654 =
        let uu____61655 = type_of ea  in
        let uu____61656 =
          let uu____61657 = type_of eb  in as_iarg uu____61657  in
        make_arrow1 uu____61655 uu____61656  in
      mk_emb em un uu____61654 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____61675 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61675 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____61680 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61680 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____61685 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61685 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____61690 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61690 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____61695 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61695 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____61700 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61700 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____61705 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61705 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____61710 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61710 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____61715 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61715 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____61724 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61725 =
          let uu____61726 =
            let uu____61731 =
              let uu____61732 = e_list e_string  in embed uu____61732 cb l
               in
            as_arg uu____61731  in
          [uu____61726]  in
        mkFV uu____61724 [] uu____61725
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____61754 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61755 =
          let uu____61756 =
            let uu____61761 =
              let uu____61762 = e_list e_string  in embed uu____61762 cb l
               in
            as_arg uu____61761  in
          [uu____61756]  in
        mkFV uu____61754 [] uu____61755
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____61784 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61785 =
          let uu____61786 =
            let uu____61791 =
              let uu____61792 = e_list e_string  in embed uu____61792 cb l
               in
            as_arg uu____61791  in
          [uu____61786]  in
        mkFV uu____61784 [] uu____61785
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____61826,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____61842,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____61858,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____61874,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____61890,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____61906,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____61922,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____61938,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____61954,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____61970,(l,uu____61972)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____61991 =
          let uu____61997 = e_list e_string  in unembed uu____61997 cb l  in
        FStar_Util.bind_opt uu____61991
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62017  -> FStar_Pervasives_Native.Some _62017)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____62019,(l,uu____62021)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____62040 =
          let uu____62046 = e_list e_string  in unembed uu____62046 cb l  in
        FStar_Util.bind_opt uu____62040
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62066  -> FStar_Pervasives_Native.Some _62066)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____62068,(l,uu____62070)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____62089 =
          let uu____62095 = e_list e_string  in unembed uu____62095 cb l  in
        FStar_Util.bind_opt uu____62089
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62115  -> FStar_Pervasives_Native.Some _62115)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____62116 ->
        ((let uu____62118 =
            let uu____62124 =
              let uu____62126 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____62126
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62124)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62118);
         FStar_Pervasives_Native.None)
     in
  let uu____62130 =
    let uu____62131 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____62131 [] []  in
  let uu____62136 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____62130 uu____62136 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____62145  -> failwith "bogus_cbs translate")
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
      let uu____62222 =
        let uu____62231 = e_list e  in unembed uu____62231 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____62222
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____62253  ->
    match uu____62253 with
    | (a,uu____62261) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____62276)::[]) when
             let uu____62293 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____62293 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____62300 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____62343 = let uu____62350 = as_arg c  in [uu____62350]  in
      int_to_t2 uu____62343
  
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
          let uu____62404 = f a  in FStar_Pervasives_Native.Some uu____62404
      | uu____62405 -> FStar_Pervasives_Native.None
  
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
          let uu____62459 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____62459
      | uu____62460 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____62504 = FStar_List.map as_a args  in
        lift_unary f uu____62504
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____62559 = FStar_List.map as_a args  in
        lift_binary f uu____62559
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____62589 = f x  in embed e_int bogus_cbs uu____62589)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____62616 = f x y  in embed e_int bogus_cbs uu____62616)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____62642 = f x  in embed e_bool bogus_cbs uu____62642)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____62680 = f x y  in embed e_bool bogus_cbs uu____62680)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____62718 = f x y  in embed e_string bogus_cbs uu____62718)
  
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
                let uu____62823 =
                  let uu____62832 = as_a a  in
                  let uu____62835 = as_b b  in (uu____62832, uu____62835)  in
                (match uu____62823 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____62850 =
                       let uu____62851 = f a1 b1  in embed_c uu____62851  in
                     FStar_Pervasives_Native.Some uu____62850
                 | uu____62852 -> FStar_Pervasives_Native.None)
            | uu____62861 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____62870 = e_list e_char  in
    let uu____62877 = FStar_String.list_of_string s  in
    embed uu____62870 bogus_cbs uu____62877
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____62916 =
        let uu____62917 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____62917  in
      embed e_int bogus_cbs uu____62916
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____62951 = arg_as_string a1  in
        (match uu____62951 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____62960 = arg_as_list e_string a2  in
             (match uu____62960 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____62978 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____62978
              | uu____62980 -> FStar_Pervasives_Native.None)
         | uu____62986 -> FStar_Pervasives_Native.None)
    | uu____62990 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____62997 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____62997
  
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
      | (_typ,uu____63059)::(a1,uu____63061)::(a2,uu____63063)::[] ->
          let uu____63080 = eq_t a1 a2  in
          (match uu____63080 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____63089 -> FStar_Pervasives_Native.None)
      | uu____63090 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____63105)::(_typ,uu____63107)::(a1,uu____63109)::(a2,uu____63111)::[]
        ->
        let uu____63132 = eq_t a1 a2  in
        (match uu____63132 with
         | FStar_Syntax_Util.Equal  ->
             let uu____63135 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____63135
         | FStar_Syntax_Util.NotEqual  ->
             let uu____63138 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____63138
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____63141 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____63156)::(_v,uu____63158)::(t1,uu____63160)::(t2,uu____63162)::
        (a1,uu____63164)::(a2,uu____63166)::[] ->
        let uu____63195 =
          let uu____63196 = eq_t t1 t2  in
          let uu____63197 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____63196 uu____63197  in
        (match uu____63195 with
         | FStar_Syntax_Util.Equal  ->
             let uu____63200 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____63200
         | FStar_Syntax_Util.NotEqual  ->
             let uu____63203 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____63203
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____63206 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____63225 =
        let uu____63227 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____63227  in
      failwith uu____63225
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____63243)::[] ->
        let uu____63252 = unembed e_range bogus_cbs a1  in
        (match uu____63252 with
         | FStar_Pervasives_Native.Some r ->
             let uu____63258 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____63258
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____63259 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63295 = arg_as_list e_char a1  in
        (match uu____63295 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63311 = arg_as_string a2  in
             (match uu____63311 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____63324 =
                    let uu____63325 = e_list e_string  in
                    embed uu____63325 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____63324
              | uu____63335 -> FStar_Pervasives_Native.None)
         | uu____63339 -> FStar_Pervasives_Native.None)
    | uu____63345 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63378 =
          let uu____63388 = arg_as_string a1  in
          let uu____63392 = arg_as_int a2  in (uu____63388, uu____63392)  in
        (match uu____63378 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1497_63416  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____63421 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63421) ()
              with | uu___1496_63424 -> FStar_Pervasives_Native.None)
         | uu____63427 -> FStar_Pervasives_Native.None)
    | uu____63437 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63470 =
          let uu____63481 = arg_as_string a1  in
          let uu____63485 = arg_as_char a2  in (uu____63481, uu____63485)  in
        (match uu____63470 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1515_63514  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____63518 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63518) ()
              with | uu___1514_63520 -> FStar_Pervasives_Native.None)
         | uu____63523 -> FStar_Pervasives_Native.None)
    | uu____63534 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____63576 =
          let uu____63590 = arg_as_string a1  in
          let uu____63594 = arg_as_int a2  in
          let uu____63597 = arg_as_int a3  in
          (uu____63590, uu____63594, uu____63597)  in
        (match uu____63576 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1538_63630  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____63635 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63635) ()
              with | uu___1537_63638 -> FStar_Pervasives_Native.None)
         | uu____63641 -> FStar_Pervasives_Native.None)
    | uu____63655 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____63715 =
          let uu____63737 = arg_as_string fn  in
          let uu____63741 = arg_as_int from_line  in
          let uu____63744 = arg_as_int from_col  in
          let uu____63747 = arg_as_int to_line  in
          let uu____63750 = arg_as_int to_col  in
          (uu____63737, uu____63741, uu____63744, uu____63747, uu____63750)
           in
        (match uu____63715 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____63785 =
                 let uu____63786 = FStar_BigInt.to_int_fs from_l  in
                 let uu____63788 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____63786 uu____63788  in
               let uu____63790 =
                 let uu____63791 = FStar_BigInt.to_int_fs to_l  in
                 let uu____63793 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____63791 uu____63793  in
               FStar_Range.mk_range fn1 uu____63785 uu____63790  in
             let uu____63795 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____63795
         | uu____63796 -> FStar_Pervasives_Native.None)
    | uu____63818 -> FStar_Pervasives_Native.None
  
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
                let uu____63908 = FStar_List.splitAt n_tvars args  in
                match uu____63908 with
                | (_tvar_args,rest_args) ->
                    let uu____63957 = FStar_List.hd rest_args  in
                    (match uu____63957 with
                     | (x,uu____63969) ->
                         let uu____63970 = unembed ea cb x  in
                         FStar_Util.map_opt uu____63970
                           (fun x1  ->
                              let uu____63976 = f x1  in
                              embed eb cb uu____63976))
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
                  let uu____64085 = FStar_List.splitAt n_tvars args  in
                  match uu____64085 with
                  | (_tvar_args,rest_args) ->
                      let uu____64134 = FStar_List.hd rest_args  in
                      (match uu____64134 with
                       | (x,uu____64146) ->
                           let uu____64147 =
                             let uu____64152 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____64152  in
                           (match uu____64147 with
                            | (y,uu____64170) ->
                                let uu____64171 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____64171
                                  (fun x1  ->
                                     let uu____64177 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____64177
                                       (fun y1  ->
                                          let uu____64183 =
                                            let uu____64184 = f x1 y1  in
                                            embed ec cb uu____64184  in
                                          FStar_Pervasives_Native.Some
                                            uu____64183))))
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
                    let uu____64312 = FStar_List.splitAt n_tvars args  in
                    match uu____64312 with
                    | (_tvar_args,rest_args) ->
                        let uu____64361 = FStar_List.hd rest_args  in
                        (match uu____64361 with
                         | (x,uu____64373) ->
                             let uu____64374 =
                               let uu____64379 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____64379  in
                             (match uu____64374 with
                              | (y,uu____64397) ->
                                  let uu____64398 =
                                    let uu____64403 =
                                      let uu____64410 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____64410  in
                                    FStar_List.hd uu____64403  in
                                  (match uu____64398 with
                                   | (z,uu____64432) ->
                                       let uu____64433 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____64433
                                         (fun x1  ->
                                            let uu____64439 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____64439
                                              (fun y1  ->
                                                 let uu____64445 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____64445
                                                   (fun z1  ->
                                                      let uu____64451 =
                                                        let uu____64452 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____64452
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____64451))))))
                     in
                  f_wrapped
  