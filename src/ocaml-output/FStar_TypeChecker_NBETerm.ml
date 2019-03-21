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
    match projectee with | Unit  -> true | uu____55932 -> false
  
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____55945 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____55967 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____55991 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____56026 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____56048 -> false
  
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
    match projectee with | Var _0 -> true | uu____56430 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____56466 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____56566 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____56685 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____56748 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____56823 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____56884 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____56903 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____56922 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____56940 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____56972 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____57065 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____57126 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____57149 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____57194 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____57291 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____57424 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____57467 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____57504 -> false
  
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
    match projectee with | TOTAL  -> true | uu____57633 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____57644 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____57655 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____57666 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____57677 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____57688 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____57699 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____57710 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CPS  -> true | uu____57721 -> false
  
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____57733 -> false
  
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
    match trm with | Accu uu____57809 -> true | uu____57821 -> false
  
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with
    | Accu (uu____57831,uu____57832) -> false
    | uu____57846 -> true
  
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
  fun uu___516_57982  ->
    if uu___516_57982
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___517_57993  ->
    if uu___517_57993
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
      | (FStar_Syntax_Util.NotEqual ,uu____58009) ->
          FStar_Syntax_Util.NotEqual
      | (uu____58010,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____58011) -> FStar_Syntax_Util.Unknown
      | (uu____58012,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____58029 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____58049),String (s2,uu____58051)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____58064,uu____58065) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____58101,Lam uu____58102) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____58191 = eq_atom a1 a2  in
          eq_and uu____58191 (fun uu____58193  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____58232 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____58232
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____58248 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____58305  ->
                        match uu____58305 with
                        | ((a1,uu____58319),(a2,uu____58321)) ->
                            let uu____58330 = eq_t a1 a2  in
                            eq_inj acc uu____58330) FStar_Syntax_Util.Equal)
                uu____58248))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____58371 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____58371
          then
            let uu____58374 =
              let uu____58375 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____58375  in
            eq_and uu____58374 (fun uu____58378  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____58385 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____58385
      | (Univ u1,Univ u2) ->
          let uu____58389 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____58389
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____58436 =
            let uu____58437 =
              let uu____58438 = t11 ()  in
              FStar_Pervasives_Native.fst uu____58438  in
            let uu____58443 =
              let uu____58444 = t21 ()  in
              FStar_Pervasives_Native.fst uu____58444  in
            eq_t uu____58437 uu____58443  in
          eq_and uu____58436
            (fun uu____58452  ->
               let uu____58453 =
                 let uu____58454 = mkAccuVar x  in r1 uu____58454  in
               let uu____58455 =
                 let uu____58456 = mkAccuVar x  in r2 uu____58456  in
               eq_t uu____58453 uu____58455)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____58457,uu____58458) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____58463,uu____58464) -> FStar_Syntax_Util.Unknown

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
          let uu____58545 = eq_arg x y  in
          eq_and uu____58545 (fun uu____58547  -> eq_args xs ys)
      | (uu____58548,uu____58549) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____58596) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____58601 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____58601
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____58630) ->
        let uu____58675 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____58686 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____58675 uu____58686
    | Accu (a,l) ->
        let uu____58703 =
          let uu____58705 = atom_to_string a  in
          let uu____58707 =
            let uu____58709 =
              let uu____58711 =
                let uu____58713 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____58713  in
              FStar_String.op_Hat uu____58711 ")"  in
            FStar_String.op_Hat ") (" uu____58709  in
          FStar_String.op_Hat uu____58705 uu____58707  in
        FStar_String.op_Hat "Accu (" uu____58703
    | Construct (fv,us,l) ->
        let uu____58751 =
          let uu____58753 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____58755 =
            let uu____58757 =
              let uu____58759 =
                let uu____58761 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____58761  in
              let uu____58767 =
                let uu____58769 =
                  let uu____58771 =
                    let uu____58773 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____58773  in
                  FStar_String.op_Hat uu____58771 "]"  in
                FStar_String.op_Hat "] [" uu____58769  in
              FStar_String.op_Hat uu____58759 uu____58767  in
            FStar_String.op_Hat ") [" uu____58757  in
          FStar_String.op_Hat uu____58753 uu____58755  in
        FStar_String.op_Hat "Construct (" uu____58751
    | FV (fv,us,l) ->
        let uu____58812 =
          let uu____58814 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____58816 =
            let uu____58818 =
              let uu____58820 =
                let uu____58822 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____58822  in
              let uu____58828 =
                let uu____58830 =
                  let uu____58832 =
                    let uu____58834 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____58834  in
                  FStar_String.op_Hat uu____58832 "]"  in
                FStar_String.op_Hat "] [" uu____58830  in
              FStar_String.op_Hat uu____58820 uu____58828  in
            FStar_String.op_Hat ") [" uu____58818  in
          FStar_String.op_Hat uu____58814 uu____58816  in
        FStar_String.op_Hat "FV (" uu____58812
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____58856 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____58856
    | Type_t u ->
        let uu____58860 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____58860
    | Arrow uu____58863 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____58909 = t ()  in FStar_Pervasives_Native.fst uu____58909
           in
        let uu____58914 =
          let uu____58916 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____58918 =
            let uu____58920 =
              let uu____58922 = t_to_string t1  in
              let uu____58924 =
                let uu____58926 =
                  let uu____58928 =
                    let uu____58930 =
                      let uu____58931 = mkAccuVar x1  in f uu____58931  in
                    t_to_string uu____58930  in
                  FStar_String.op_Hat uu____58928 "}"  in
                FStar_String.op_Hat "{" uu____58926  in
              FStar_String.op_Hat uu____58922 uu____58924  in
            FStar_String.op_Hat ":" uu____58920  in
          FStar_String.op_Hat uu____58916 uu____58918  in
        FStar_String.op_Hat "Refinement " uu____58914
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____58938 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____58938
    | Quote uu____58941 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____58948) ->
        let uu____58965 =
          let uu____58967 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____58967  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____58965
    | Lazy (FStar_Util.Inr (uu____58969,et),uu____58971) ->
        let uu____58988 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____58988
    | Rec
        (uu____58991,uu____58992,l,uu____58994,uu____58995,uu____58996,uu____58997)
        ->
        let uu____59042 =
          let uu____59044 =
            let uu____59046 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____59046  in
          FStar_String.op_Hat uu____59044 ")"  in
        FStar_String.op_Hat "Rec (" uu____59042

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____59057 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____59057
    | Match (t,uu____59061,uu____59062) ->
        let uu____59085 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____59085

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____59089 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____59089 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____59096 =
      FStar_All.pipe_right args (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____59096 (FStar_String.concat " ")

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
        let uu____59567 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____59567 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____59588 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____59588 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____59629  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____59644  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____59687 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____59687
         then
           let uu____59711 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____59711
         else ());
        (let uu____59716 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____59716
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li =
              let uu____59750 = FStar_Dyn.mkdyn x  in (uu____59750, et)  in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____59778 'a .
    'Auu____59778 ->
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
              let uu____59829 = FStar_Common.force_thunk thunk1  in
              f uu____59829
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____59849 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____59849
              then
                let res =
                  let uu____59878 = FStar_Common.force_thunk thunk1  in
                  f uu____59878  in
                ((let uu____59880 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____59880
                  then
                    let uu____59904 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____59906 =
                      FStar_Syntax_Print.emb_typ_to_string et'  in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____59904
                      uu____59906
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____59915 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____59915
                  then
                    let uu____59939 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n"
                      uu____59939
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____59944 ->
              let aopt = f x  in
              ((let uu____59949 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____59949
                then
                  let uu____59973 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n"
                    uu____59973
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
  let uu____60041 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____60041 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____60075 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____60080 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____60075 uu____60080 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____60121 -> FStar_Pervasives_Native.None  in
  let uu____60123 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____60128 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____60123 uu____60128 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____60170 -> FStar_Pervasives_Native.None  in
  let uu____60172 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____60177 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____60172 uu____60177 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____60219)) -> FStar_Pervasives_Native.Some s1
    | uu____60223 -> FStar_Pervasives_Native.None  in
  let uu____60225 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____60230 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____60225 uu____60230 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____60265 -> FStar_Pervasives_Native.None  in
  let uu____60266 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____60271 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____60266 uu____60271 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____60292 =
        let uu____60300 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____60300, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____60292  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____60325  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____60326 =
                 let uu____60327 =
                   let uu____60332 = type_of ea  in as_iarg uu____60332  in
                 [uu____60327]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____60326
           | FStar_Pervasives_Native.Some x ->
               let uu____60342 =
                 let uu____60343 =
                   let uu____60348 = embed ea cb x  in as_arg uu____60348  in
                 let uu____60349 =
                   let uu____60356 =
                     let uu____60361 = type_of ea  in as_iarg uu____60361  in
                   [uu____60356]  in
                 uu____60343 :: uu____60349  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____60342)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____60428)::uu____60429::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____60456 = unembed ea cb a  in
               FStar_Util.bind_opt uu____60456
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____60465 -> FStar_Pervasives_Native.None)
       in
    let uu____60468 =
      let uu____60469 =
        let uu____60470 = let uu____60475 = type_of ea  in as_arg uu____60475
           in
        [uu____60470]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____60469
       in
    mk_emb em un uu____60468 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____60522 =
          let uu____60530 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____60530, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60522  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____60561  ->
             let uu____60562 =
               let uu____60563 =
                 let uu____60568 =
                   embed eb cb (FStar_Pervasives_Native.snd x)  in
                 as_arg uu____60568  in
               let uu____60569 =
                 let uu____60576 =
                   let uu____60581 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____60581  in
                 let uu____60582 =
                   let uu____60589 =
                     let uu____60594 = type_of eb  in as_iarg uu____60594  in
                   let uu____60595 =
                     let uu____60602 =
                       let uu____60607 = type_of ea  in as_iarg uu____60607
                        in
                     [uu____60602]  in
                   uu____60589 :: uu____60595  in
                 uu____60576 :: uu____60582  in
               uu____60563 :: uu____60569  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____60562)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____60675)::(a,uu____60677)::uu____60678::uu____60679::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____60718 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____60718
                   (fun a1  ->
                      let uu____60728 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____60728
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____60741 -> FStar_Pervasives_Native.None)
         in
      let uu____60746 =
        let uu____60747 =
          let uu____60748 =
            let uu____60753 = type_of eb  in as_arg uu____60753  in
          let uu____60754 =
            let uu____60761 =
              let uu____60766 = type_of ea  in as_arg uu____60766  in
            [uu____60761]  in
          uu____60748 :: uu____60754  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____60747
         in
      mk_emb em un uu____60746 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____60819 =
          let uu____60827 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____60827, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60819  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____60859  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____60861 =
                   let uu____60862 =
                     let uu____60867 = embed ea cb a  in as_arg uu____60867
                      in
                   let uu____60868 =
                     let uu____60875 =
                       let uu____60880 = type_of eb  in as_iarg uu____60880
                        in
                     let uu____60881 =
                       let uu____60888 =
                         let uu____60893 = type_of ea  in as_iarg uu____60893
                          in
                       [uu____60888]  in
                     uu____60875 :: uu____60881  in
                   uu____60862 :: uu____60868  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____60861
             | FStar_Util.Inr b ->
                 let uu____60911 =
                   let uu____60912 =
                     let uu____60917 = embed eb cb b  in as_arg uu____60917
                      in
                   let uu____60918 =
                     let uu____60925 =
                       let uu____60930 = type_of eb  in as_iarg uu____60930
                        in
                     let uu____60931 =
                       let uu____60938 =
                         let uu____60943 = type_of ea  in as_iarg uu____60943
                          in
                       [uu____60938]  in
                     uu____60925 :: uu____60931  in
                   uu____60912 :: uu____60918  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____60911)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____61005)::uu____61006::uu____61007::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____61042 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____61042
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____61058)::uu____61059::uu____61060::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____61095 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____61095
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____61108 -> FStar_Pervasives_Native.None)
         in
      let uu____61113 =
        let uu____61114 =
          let uu____61115 =
            let uu____61120 = type_of eb  in as_arg uu____61120  in
          let uu____61121 =
            let uu____61128 =
              let uu____61133 = type_of ea  in as_arg uu____61133  in
            [uu____61128]  in
          uu____61115 :: uu____61121  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____61114
         in
      mk_emb em un uu____61113 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____61182 -> FStar_Pervasives_Native.None  in
  let uu____61183 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____61188 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____61183 uu____61188 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____61209 =
        let uu____61217 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____61217, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____61209  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____61244  ->
           let typ = let uu____61246 = type_of ea  in as_iarg uu____61246  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____61267 =
               let uu____61268 = as_arg tl1  in
               let uu____61273 =
                 let uu____61280 =
                   let uu____61285 = embed ea cb hd1  in as_arg uu____61285
                    in
                 [uu____61280; typ]  in
               uu____61268 :: uu____61273  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____61267
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____61333,uu____61334) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____61354,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____61357,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____61358))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____61386 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____61386
                 (fun hd2  ->
                    let uu____61394 = un cb tl1  in
                    FStar_Util.bind_opt uu____61394
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____61410,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____61435 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____61435
                 (fun hd2  ->
                    let uu____61443 = un cb tl1  in
                    FStar_Util.bind_opt uu____61443
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____61458 -> FStar_Pervasives_Native.None)
       in
    let uu____61461 =
      let uu____61462 =
        let uu____61463 = let uu____61468 = type_of ea  in as_arg uu____61468
           in
        [uu____61463]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____61462
       in
    mk_emb em un uu____61461 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____61541  ->
             Lam
               ((fun tas  ->
                   let uu____61571 =
                     let uu____61574 = FStar_List.hd tas  in
                     unembed ea cb uu____61574  in
                   match uu____61571 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____61576 = f a  in embed eb cb uu____61576
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____61589  ->
                     let uu____61592 = type_of eb  in as_arg uu____61592)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____61650 =
                 let uu____61653 =
                   let uu____61654 =
                     let uu____61655 =
                       let uu____61660 = embed ea cb x  in as_arg uu____61660
                        in
                     [uu____61655]  in
                   cb.iapp lam1 uu____61654  in
                 unembed eb cb uu____61653  in
               match uu____61650 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____61674 =
        let uu____61675 = type_of ea  in
        let uu____61676 =
          let uu____61677 = type_of eb  in as_iarg uu____61677  in
        make_arrow1 uu____61675 uu____61676  in
      mk_emb em un uu____61674 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____61695 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61695 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____61700 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61700 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____61705 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61705 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____61710 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61710 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____61715 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61715 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____61720 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61720 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____61725 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61725 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____61730 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61730 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____61735 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61735 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____61744 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61745 =
          let uu____61746 =
            let uu____61751 =
              let uu____61752 = e_list e_string  in embed uu____61752 cb l
               in
            as_arg uu____61751  in
          [uu____61746]  in
        mkFV uu____61744 [] uu____61745
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____61774 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61775 =
          let uu____61776 =
            let uu____61781 =
              let uu____61782 = e_list e_string  in embed uu____61782 cb l
               in
            as_arg uu____61781  in
          [uu____61776]  in
        mkFV uu____61774 [] uu____61775
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____61804 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61805 =
          let uu____61806 =
            let uu____61811 =
              let uu____61812 = e_list e_string  in embed uu____61812 cb l
               in
            as_arg uu____61811  in
          [uu____61806]  in
        mkFV uu____61804 [] uu____61805
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____61846,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____61862,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____61878,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____61894,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____61910,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____61926,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____61942,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____61958,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____61974,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____61990,(l,uu____61992)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____62011 =
          let uu____62017 = e_list e_string  in unembed uu____62017 cb l  in
        FStar_Util.bind_opt uu____62011
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62037  -> FStar_Pervasives_Native.Some _62037)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____62039,(l,uu____62041)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____62060 =
          let uu____62066 = e_list e_string  in unembed uu____62066 cb l  in
        FStar_Util.bind_opt uu____62060
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62086  -> FStar_Pervasives_Native.Some _62086)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____62088,(l,uu____62090)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____62109 =
          let uu____62115 = e_list e_string  in unembed uu____62115 cb l  in
        FStar_Util.bind_opt uu____62109
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62135  -> FStar_Pervasives_Native.Some _62135)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____62136 ->
        ((let uu____62138 =
            let uu____62144 =
              let uu____62146 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____62146
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62144)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62138);
         FStar_Pervasives_Native.None)
     in
  let uu____62150 =
    let uu____62151 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____62151 [] []  in
  let uu____62156 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____62150 uu____62156 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____62165  -> failwith "bogus_cbs translate")
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
      let uu____62242 =
        let uu____62251 = e_list e  in unembed uu____62251 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____62242
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____62273  ->
    match uu____62273 with
    | (a,uu____62281) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____62296)::[]) when
             let uu____62313 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____62313 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____62320 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____62363 = let uu____62370 = as_arg c  in [uu____62370]  in
      int_to_t2 uu____62363
  
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
          let uu____62424 = f a  in FStar_Pervasives_Native.Some uu____62424
      | uu____62425 -> FStar_Pervasives_Native.None
  
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
          let uu____62479 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____62479
      | uu____62480 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____62524 = FStar_List.map as_a args  in
        lift_unary f uu____62524
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____62579 = FStar_List.map as_a args  in
        lift_binary f uu____62579
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____62609 = f x  in embed e_int bogus_cbs uu____62609)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____62636 = f x y  in embed e_int bogus_cbs uu____62636)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____62662 = f x  in embed e_bool bogus_cbs uu____62662)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____62700 = f x y  in embed e_bool bogus_cbs uu____62700)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____62738 = f x y  in embed e_string bogus_cbs uu____62738)
  
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
                let uu____62843 =
                  let uu____62852 = as_a a  in
                  let uu____62855 = as_b b  in (uu____62852, uu____62855)  in
                (match uu____62843 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____62870 =
                       let uu____62871 = f a1 b1  in embed_c uu____62871  in
                     FStar_Pervasives_Native.Some uu____62870
                 | uu____62872 -> FStar_Pervasives_Native.None)
            | uu____62881 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____62890 = e_list e_char  in
    let uu____62897 = FStar_String.list_of_string s  in
    embed uu____62890 bogus_cbs uu____62897
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____62936 =
        let uu____62937 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____62937  in
      embed e_int bogus_cbs uu____62936
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____62971 = arg_as_string a1  in
        (match uu____62971 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____62980 = arg_as_list e_string a2  in
             (match uu____62980 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____62998 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____62998
              | uu____63000 -> FStar_Pervasives_Native.None)
         | uu____63006 -> FStar_Pervasives_Native.None)
    | uu____63010 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____63017 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____63017
  
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
      | (_typ,uu____63079)::(a1,uu____63081)::(a2,uu____63083)::[] ->
          let uu____63100 = eq_t a1 a2  in
          (match uu____63100 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____63109 -> FStar_Pervasives_Native.None)
      | uu____63110 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____63125)::(_typ,uu____63127)::(a1,uu____63129)::(a2,uu____63131)::[]
        ->
        let uu____63152 = eq_t a1 a2  in
        (match uu____63152 with
         | FStar_Syntax_Util.Equal  ->
             let uu____63155 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____63155
         | FStar_Syntax_Util.NotEqual  ->
             let uu____63158 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____63158
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____63161 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____63176)::(_v,uu____63178)::(t1,uu____63180)::(t2,uu____63182)::
        (a1,uu____63184)::(a2,uu____63186)::[] ->
        let uu____63215 =
          let uu____63216 = eq_t t1 t2  in
          let uu____63217 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____63216 uu____63217  in
        (match uu____63215 with
         | FStar_Syntax_Util.Equal  ->
             let uu____63220 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____63220
         | FStar_Syntax_Util.NotEqual  ->
             let uu____63223 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____63223
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____63226 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____63245 =
        let uu____63247 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____63247  in
      failwith uu____63245
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____63263)::[] ->
        let uu____63272 = unembed e_range bogus_cbs a1  in
        (match uu____63272 with
         | FStar_Pervasives_Native.Some r ->
             let uu____63278 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____63278
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____63279 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63315 = arg_as_list e_char a1  in
        (match uu____63315 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63331 = arg_as_string a2  in
             (match uu____63331 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____63344 =
                    let uu____63345 = e_list e_string  in
                    embed uu____63345 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____63344
              | uu____63355 -> FStar_Pervasives_Native.None)
         | uu____63359 -> FStar_Pervasives_Native.None)
    | uu____63365 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63398 =
          let uu____63408 = arg_as_string a1  in
          let uu____63412 = arg_as_int a2  in (uu____63408, uu____63412)  in
        (match uu____63398 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1497_63436  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____63441 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63441) ()
              with | uu___1496_63444 -> FStar_Pervasives_Native.None)
         | uu____63447 -> FStar_Pervasives_Native.None)
    | uu____63457 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63490 =
          let uu____63501 = arg_as_string a1  in
          let uu____63505 = arg_as_char a2  in (uu____63501, uu____63505)  in
        (match uu____63490 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1515_63534  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____63538 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63538) ()
              with | uu___1514_63540 -> FStar_Pervasives_Native.None)
         | uu____63543 -> FStar_Pervasives_Native.None)
    | uu____63554 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____63596 =
          let uu____63610 = arg_as_string a1  in
          let uu____63614 = arg_as_int a2  in
          let uu____63617 = arg_as_int a3  in
          (uu____63610, uu____63614, uu____63617)  in
        (match uu____63596 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1538_63650  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____63655 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63655) ()
              with | uu___1537_63658 -> FStar_Pervasives_Native.None)
         | uu____63661 -> FStar_Pervasives_Native.None)
    | uu____63675 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____63735 =
          let uu____63757 = arg_as_string fn  in
          let uu____63761 = arg_as_int from_line  in
          let uu____63764 = arg_as_int from_col  in
          let uu____63767 = arg_as_int to_line  in
          let uu____63770 = arg_as_int to_col  in
          (uu____63757, uu____63761, uu____63764, uu____63767, uu____63770)
           in
        (match uu____63735 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____63805 =
                 let uu____63806 = FStar_BigInt.to_int_fs from_l  in
                 let uu____63808 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____63806 uu____63808  in
               let uu____63810 =
                 let uu____63811 = FStar_BigInt.to_int_fs to_l  in
                 let uu____63813 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____63811 uu____63813  in
               FStar_Range.mk_range fn1 uu____63805 uu____63810  in
             let uu____63815 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____63815
         | uu____63816 -> FStar_Pervasives_Native.None)
    | uu____63838 -> FStar_Pervasives_Native.None
  
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
                let uu____63928 = FStar_List.splitAt n_tvars args  in
                match uu____63928 with
                | (_tvar_args,rest_args) ->
                    let uu____63977 = FStar_List.hd rest_args  in
                    (match uu____63977 with
                     | (x,uu____63989) ->
                         let uu____63990 = unembed ea cb x  in
                         FStar_Util.map_opt uu____63990
                           (fun x1  ->
                              let uu____63996 = f x1  in
                              embed eb cb uu____63996))
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
                  let uu____64105 = FStar_List.splitAt n_tvars args  in
                  match uu____64105 with
                  | (_tvar_args,rest_args) ->
                      let uu____64154 = FStar_List.hd rest_args  in
                      (match uu____64154 with
                       | (x,uu____64166) ->
                           let uu____64167 =
                             let uu____64172 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____64172  in
                           (match uu____64167 with
                            | (y,uu____64190) ->
                                let uu____64191 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____64191
                                  (fun x1  ->
                                     let uu____64197 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____64197
                                       (fun y1  ->
                                          let uu____64203 =
                                            let uu____64204 = f x1 y1  in
                                            embed ec cb uu____64204  in
                                          FStar_Pervasives_Native.Some
                                            uu____64203))))
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
                    let uu____64332 = FStar_List.splitAt n_tvars args  in
                    match uu____64332 with
                    | (_tvar_args,rest_args) ->
                        let uu____64381 = FStar_List.hd rest_args  in
                        (match uu____64381 with
                         | (x,uu____64393) ->
                             let uu____64394 =
                               let uu____64399 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____64399  in
                             (match uu____64394 with
                              | (y,uu____64417) ->
                                  let uu____64418 =
                                    let uu____64423 =
                                      let uu____64430 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____64430  in
                                    FStar_List.hd uu____64423  in
                                  (match uu____64418 with
                                   | (z,uu____64452) ->
                                       let uu____64453 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____64453
                                         (fun x1  ->
                                            let uu____64459 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____64459
                                              (fun y1  ->
                                                 let uu____64465 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____64465
                                                   (fun z1  ->
                                                      let uu____64471 =
                                                        let uu____64472 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____64472
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____64471))))))
                     in
                  f_wrapped
  