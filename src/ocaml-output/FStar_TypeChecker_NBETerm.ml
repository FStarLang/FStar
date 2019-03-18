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
    match projectee with | Unit  -> true | uu____55898 -> false
  
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____55911 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____55933 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____55957 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____55992 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____56014 -> false
  
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
    match projectee with | Var _0 -> true | uu____56396 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____56432 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____56532 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____56651 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____56714 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____56789 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____56850 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____56869 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____56888 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____56906 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____56938 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____57031 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____57092 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____57115 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____57160 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____57257 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____57390 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____57433 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____57470 -> false
  
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
    match projectee with | TOTAL  -> true | uu____57599 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____57610 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____57621 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____57632 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____57643 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____57654 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____57665 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____57676 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CPS  -> true | uu____57687 -> false
  
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____57699 -> false
  
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
    match trm with | Accu uu____57775 -> true | uu____57787 -> false
  
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with
    | Accu (uu____57797,uu____57798) -> false
    | uu____57812 -> true
  
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
  fun uu___516_57948  ->
    if uu___516_57948
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___517_57959  ->
    if uu___517_57959
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
      | (FStar_Syntax_Util.NotEqual ,uu____57975) ->
          FStar_Syntax_Util.NotEqual
      | (uu____57976,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____57977) -> FStar_Syntax_Util.Unknown
      | (uu____57978,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____57995 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____58015),String (s2,uu____58017)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____58030,uu____58031) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____58067,Lam uu____58068) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____58157 = eq_atom a1 a2  in
          eq_and uu____58157 (fun uu____58159  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____58198 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____58198
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____58214 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____58271  ->
                        match uu____58271 with
                        | ((a1,uu____58285),(a2,uu____58287)) ->
                            let uu____58296 = eq_t a1 a2  in
                            eq_inj acc uu____58296) FStar_Syntax_Util.Equal)
                uu____58214))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____58337 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____58337
          then
            let uu____58340 =
              let uu____58341 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____58341  in
            eq_and uu____58340 (fun uu____58344  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____58351 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____58351
      | (Univ u1,Univ u2) ->
          let uu____58355 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____58355
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____58402 =
            let uu____58403 =
              let uu____58404 = t11 ()  in
              FStar_Pervasives_Native.fst uu____58404  in
            let uu____58409 =
              let uu____58410 = t21 ()  in
              FStar_Pervasives_Native.fst uu____58410  in
            eq_t uu____58403 uu____58409  in
          eq_and uu____58402
            (fun uu____58418  ->
               let uu____58419 =
                 let uu____58420 = mkAccuVar x  in r1 uu____58420  in
               let uu____58421 =
                 let uu____58422 = mkAccuVar x  in r2 uu____58422  in
               eq_t uu____58419 uu____58421)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____58423,uu____58424) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____58429,uu____58430) -> FStar_Syntax_Util.Unknown

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
          let uu____58511 = eq_arg x y  in
          eq_and uu____58511 (fun uu____58513  -> eq_args xs ys)
      | (uu____58514,uu____58515) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____58562) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____58567 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____58567
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____58596) ->
        let uu____58641 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____58652 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____58641 uu____58652
    | Accu (a,l) ->
        let uu____58669 =
          let uu____58671 = atom_to_string a  in
          let uu____58673 =
            let uu____58675 =
              let uu____58677 =
                let uu____58679 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____58679  in
              FStar_String.op_Hat uu____58677 ")"  in
            FStar_String.op_Hat ") (" uu____58675  in
          FStar_String.op_Hat uu____58671 uu____58673  in
        FStar_String.op_Hat "Accu (" uu____58669
    | Construct (fv,us,l) ->
        let uu____58717 =
          let uu____58719 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____58721 =
            let uu____58723 =
              let uu____58725 =
                let uu____58727 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____58727  in
              let uu____58733 =
                let uu____58735 =
                  let uu____58737 =
                    let uu____58739 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____58739  in
                  FStar_String.op_Hat uu____58737 "]"  in
                FStar_String.op_Hat "] [" uu____58735  in
              FStar_String.op_Hat uu____58725 uu____58733  in
            FStar_String.op_Hat ") [" uu____58723  in
          FStar_String.op_Hat uu____58719 uu____58721  in
        FStar_String.op_Hat "Construct (" uu____58717
    | FV (fv,us,l) ->
        let uu____58778 =
          let uu____58780 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____58782 =
            let uu____58784 =
              let uu____58786 =
                let uu____58788 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____58788  in
              let uu____58794 =
                let uu____58796 =
                  let uu____58798 =
                    let uu____58800 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____58800  in
                  FStar_String.op_Hat uu____58798 "]"  in
                FStar_String.op_Hat "] [" uu____58796  in
              FStar_String.op_Hat uu____58786 uu____58794  in
            FStar_String.op_Hat ") [" uu____58784  in
          FStar_String.op_Hat uu____58780 uu____58782  in
        FStar_String.op_Hat "FV (" uu____58778
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____58822 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____58822
    | Type_t u ->
        let uu____58826 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____58826
    | Arrow uu____58829 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____58875 = t ()  in FStar_Pervasives_Native.fst uu____58875
           in
        let uu____58880 =
          let uu____58882 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____58884 =
            let uu____58886 =
              let uu____58888 = t_to_string t1  in
              let uu____58890 =
                let uu____58892 =
                  let uu____58894 =
                    let uu____58896 =
                      let uu____58897 = mkAccuVar x1  in f uu____58897  in
                    t_to_string uu____58896  in
                  FStar_String.op_Hat uu____58894 "}"  in
                FStar_String.op_Hat "{" uu____58892  in
              FStar_String.op_Hat uu____58888 uu____58890  in
            FStar_String.op_Hat ":" uu____58886  in
          FStar_String.op_Hat uu____58882 uu____58884  in
        FStar_String.op_Hat "Refinement " uu____58880
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____58904 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____58904
    | Quote uu____58907 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____58914) ->
        let uu____58931 =
          let uu____58933 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____58933  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____58931
    | Lazy (FStar_Util.Inr (uu____58935,et),uu____58937) ->
        let uu____58954 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____58954
    | Rec
        (uu____58957,uu____58958,l,uu____58960,uu____58961,uu____58962,uu____58963)
        ->
        let uu____59008 =
          let uu____59010 =
            let uu____59012 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____59012  in
          FStar_String.op_Hat uu____59010 ")"  in
        FStar_String.op_Hat "Rec (" uu____59008

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____59023 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____59023
    | Match (t,uu____59027,uu____59028) ->
        let uu____59051 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____59051

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____59055 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____59055 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____59062 =
      FStar_All.pipe_right args (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____59062 (FStar_String.concat " ")

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
        let uu____59533 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____59533 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____59554 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____59554 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____59595  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____59610  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____59653 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____59653
         then
           let uu____59677 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____59677
         else ());
        (let uu____59682 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____59682
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li =
              let uu____59716 = FStar_Dyn.mkdyn x  in (uu____59716, et)  in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____59744 'a .
    'Auu____59744 ->
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
              let uu____59795 = FStar_Common.force_thunk thunk1  in
              f uu____59795
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____59815 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____59815
              then
                let res =
                  let uu____59844 = FStar_Common.force_thunk thunk1  in
                  f uu____59844  in
                ((let uu____59846 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____59846
                  then
                    let uu____59870 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____59872 =
                      FStar_Syntax_Print.emb_typ_to_string et'  in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____59870
                      uu____59872
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____59881 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____59881
                  then
                    let uu____59905 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n"
                      uu____59905
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____59910 ->
              let aopt = f x  in
              ((let uu____59915 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____59915
                then
                  let uu____59939 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n"
                    uu____59939
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
  let uu____60007 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____60007 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____60041 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____60046 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____60041 uu____60046 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____60087 -> FStar_Pervasives_Native.None  in
  let uu____60089 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____60094 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____60089 uu____60094 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____60136 -> FStar_Pervasives_Native.None  in
  let uu____60138 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____60143 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____60138 uu____60143 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____60185)) -> FStar_Pervasives_Native.Some s1
    | uu____60189 -> FStar_Pervasives_Native.None  in
  let uu____60191 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____60196 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____60191 uu____60196 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____60231 -> FStar_Pervasives_Native.None  in
  let uu____60232 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____60237 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____60232 uu____60237 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____60258 =
        let uu____60266 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____60266, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____60258  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____60291  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____60292 =
                 let uu____60293 =
                   let uu____60298 = type_of ea  in as_iarg uu____60298  in
                 [uu____60293]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____60292
           | FStar_Pervasives_Native.Some x ->
               let uu____60308 =
                 let uu____60309 =
                   let uu____60314 = embed ea cb x  in as_arg uu____60314  in
                 let uu____60315 =
                   let uu____60322 =
                     let uu____60327 = type_of ea  in as_iarg uu____60327  in
                   [uu____60322]  in
                 uu____60309 :: uu____60315  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____60308)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____60394)::uu____60395::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____60422 = unembed ea cb a  in
               FStar_Util.bind_opt uu____60422
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____60431 -> FStar_Pervasives_Native.None)
       in
    let uu____60434 =
      let uu____60435 =
        let uu____60436 = let uu____60441 = type_of ea  in as_arg uu____60441
           in
        [uu____60436]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____60435
       in
    mk_emb em un uu____60434 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____60488 =
          let uu____60496 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____60496, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60488  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____60527  ->
             let uu____60528 =
               let uu____60529 =
                 let uu____60534 =
                   embed eb cb (FStar_Pervasives_Native.snd x)  in
                 as_arg uu____60534  in
               let uu____60535 =
                 let uu____60542 =
                   let uu____60547 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____60547  in
                 let uu____60548 =
                   let uu____60555 =
                     let uu____60560 = type_of eb  in as_iarg uu____60560  in
                   let uu____60561 =
                     let uu____60568 =
                       let uu____60573 = type_of ea  in as_iarg uu____60573
                        in
                     [uu____60568]  in
                   uu____60555 :: uu____60561  in
                 uu____60542 :: uu____60548  in
               uu____60529 :: uu____60535  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____60528)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____60641)::(a,uu____60643)::uu____60644::uu____60645::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____60684 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____60684
                   (fun a1  ->
                      let uu____60694 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____60694
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____60707 -> FStar_Pervasives_Native.None)
         in
      let uu____60712 =
        let uu____60713 =
          let uu____60714 =
            let uu____60719 = type_of eb  in as_arg uu____60719  in
          let uu____60720 =
            let uu____60727 =
              let uu____60732 = type_of ea  in as_arg uu____60732  in
            [uu____60727]  in
          uu____60714 :: uu____60720  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____60713
         in
      mk_emb em un uu____60712 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____60785 =
          let uu____60793 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____60793, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60785  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____60825  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____60827 =
                   let uu____60828 =
                     let uu____60833 = embed ea cb a  in as_arg uu____60833
                      in
                   let uu____60834 =
                     let uu____60841 =
                       let uu____60846 = type_of eb  in as_iarg uu____60846
                        in
                     let uu____60847 =
                       let uu____60854 =
                         let uu____60859 = type_of ea  in as_iarg uu____60859
                          in
                       [uu____60854]  in
                     uu____60841 :: uu____60847  in
                   uu____60828 :: uu____60834  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____60827
             | FStar_Util.Inr b ->
                 let uu____60877 =
                   let uu____60878 =
                     let uu____60883 = embed eb cb b  in as_arg uu____60883
                      in
                   let uu____60884 =
                     let uu____60891 =
                       let uu____60896 = type_of eb  in as_iarg uu____60896
                        in
                     let uu____60897 =
                       let uu____60904 =
                         let uu____60909 = type_of ea  in as_iarg uu____60909
                          in
                       [uu____60904]  in
                     uu____60891 :: uu____60897  in
                   uu____60878 :: uu____60884  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____60877)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____60971)::uu____60972::uu____60973::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____61008 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____61008
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____61024)::uu____61025::uu____61026::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____61061 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____61061
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____61074 -> FStar_Pervasives_Native.None)
         in
      let uu____61079 =
        let uu____61080 =
          let uu____61081 =
            let uu____61086 = type_of eb  in as_arg uu____61086  in
          let uu____61087 =
            let uu____61094 =
              let uu____61099 = type_of ea  in as_arg uu____61099  in
            [uu____61094]  in
          uu____61081 :: uu____61087  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____61080
         in
      mk_emb em un uu____61079 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____61148 -> FStar_Pervasives_Native.None  in
  let uu____61149 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____61154 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____61149 uu____61154 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____61175 =
        let uu____61183 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____61183, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____61175  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____61210  ->
           let typ = let uu____61212 = type_of ea  in as_iarg uu____61212  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____61233 =
               let uu____61234 = as_arg tl1  in
               let uu____61239 =
                 let uu____61246 =
                   let uu____61251 = embed ea cb hd1  in as_arg uu____61251
                    in
                 [uu____61246; typ]  in
               uu____61234 :: uu____61239  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____61233
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____61299,uu____61300) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____61320,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____61323,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____61324))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____61352 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____61352
                 (fun hd2  ->
                    let uu____61360 = un cb tl1  in
                    FStar_Util.bind_opt uu____61360
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____61376,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____61401 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____61401
                 (fun hd2  ->
                    let uu____61409 = un cb tl1  in
                    FStar_Util.bind_opt uu____61409
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____61424 -> FStar_Pervasives_Native.None)
       in
    let uu____61427 =
      let uu____61428 =
        let uu____61429 = let uu____61434 = type_of ea  in as_arg uu____61434
           in
        [uu____61429]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____61428
       in
    mk_emb em un uu____61427 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____61507  ->
             Lam
               ((fun tas  ->
                   let uu____61537 =
                     let uu____61540 = FStar_List.hd tas  in
                     unembed ea cb uu____61540  in
                   match uu____61537 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____61542 = f a  in embed eb cb uu____61542
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____61555  ->
                     let uu____61558 = type_of eb  in as_arg uu____61558)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____61616 =
                 let uu____61619 =
                   let uu____61620 =
                     let uu____61621 =
                       let uu____61626 = embed ea cb x  in as_arg uu____61626
                        in
                     [uu____61621]  in
                   cb.iapp lam1 uu____61620  in
                 unembed eb cb uu____61619  in
               match uu____61616 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____61640 =
        let uu____61641 = type_of ea  in
        let uu____61642 =
          let uu____61643 = type_of eb  in as_iarg uu____61643  in
        make_arrow1 uu____61641 uu____61642  in
      mk_emb em un uu____61640 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____61661 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61661 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____61666 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61666 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____61671 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61671 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____61676 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61676 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____61681 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61681 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____61686 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61686 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____61691 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61691 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____61696 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61696 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____61701 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61701 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____61710 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61711 =
          let uu____61712 =
            let uu____61717 =
              let uu____61718 = e_list e_string  in embed uu____61718 cb l
               in
            as_arg uu____61717  in
          [uu____61712]  in
        mkFV uu____61710 [] uu____61711
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____61740 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61741 =
          let uu____61742 =
            let uu____61747 =
              let uu____61748 = e_list e_string  in embed uu____61748 cb l
               in
            as_arg uu____61747  in
          [uu____61742]  in
        mkFV uu____61740 [] uu____61741
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____61770 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61771 =
          let uu____61772 =
            let uu____61777 =
              let uu____61778 = e_list e_string  in embed uu____61778 cb l
               in
            as_arg uu____61777  in
          [uu____61772]  in
        mkFV uu____61770 [] uu____61771
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____61812,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____61828,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____61844,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____61860,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____61876,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____61892,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____61908,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____61924,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____61940,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____61956,(l,uu____61958)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____61977 =
          let uu____61983 = e_list e_string  in unembed uu____61983 cb l  in
        FStar_Util.bind_opt uu____61977
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62003  -> FStar_Pervasives_Native.Some _62003)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____62005,(l,uu____62007)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____62026 =
          let uu____62032 = e_list e_string  in unembed uu____62032 cb l  in
        FStar_Util.bind_opt uu____62026
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62052  -> FStar_Pervasives_Native.Some _62052)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____62054,(l,uu____62056)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____62075 =
          let uu____62081 = e_list e_string  in unembed uu____62081 cb l  in
        FStar_Util.bind_opt uu____62075
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62101  -> FStar_Pervasives_Native.Some _62101)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____62102 ->
        ((let uu____62104 =
            let uu____62110 =
              let uu____62112 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____62112
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62110)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62104);
         FStar_Pervasives_Native.None)
     in
  let uu____62116 =
    let uu____62117 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____62117 [] []  in
  let uu____62122 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____62116 uu____62122 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____62131  -> failwith "bogus_cbs translate")
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
      let uu____62208 =
        let uu____62217 = e_list e  in unembed uu____62217 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____62208
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____62239  ->
    match uu____62239 with
    | (a,uu____62247) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____62262)::[]) when
             let uu____62279 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____62279 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____62286 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____62329 = let uu____62336 = as_arg c  in [uu____62336]  in
      int_to_t2 uu____62329
  
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
          let uu____62390 = f a  in FStar_Pervasives_Native.Some uu____62390
      | uu____62391 -> FStar_Pervasives_Native.None
  
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
          let uu____62445 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____62445
      | uu____62446 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____62490 = FStar_List.map as_a args  in
        lift_unary f uu____62490
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____62545 = FStar_List.map as_a args  in
        lift_binary f uu____62545
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____62575 = f x  in embed e_int bogus_cbs uu____62575)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____62602 = f x y  in embed e_int bogus_cbs uu____62602)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____62628 = f x  in embed e_bool bogus_cbs uu____62628)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____62666 = f x y  in embed e_bool bogus_cbs uu____62666)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____62704 = f x y  in embed e_string bogus_cbs uu____62704)
  
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
                let uu____62809 =
                  let uu____62818 = as_a a  in
                  let uu____62821 = as_b b  in (uu____62818, uu____62821)  in
                (match uu____62809 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____62836 =
                       let uu____62837 = f a1 b1  in embed_c uu____62837  in
                     FStar_Pervasives_Native.Some uu____62836
                 | uu____62838 -> FStar_Pervasives_Native.None)
            | uu____62847 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____62856 = e_list e_char  in
    let uu____62863 = FStar_String.list_of_string s  in
    embed uu____62856 bogus_cbs uu____62863
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____62902 =
        let uu____62903 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____62903  in
      embed e_int bogus_cbs uu____62902
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____62937 = arg_as_string a1  in
        (match uu____62937 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____62946 = arg_as_list e_string a2  in
             (match uu____62946 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____62964 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____62964
              | uu____62966 -> FStar_Pervasives_Native.None)
         | uu____62972 -> FStar_Pervasives_Native.None)
    | uu____62976 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____62983 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____62983
  
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
      | (_typ,uu____63045)::(a1,uu____63047)::(a2,uu____63049)::[] ->
          let uu____63066 = eq_t a1 a2  in
          (match uu____63066 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____63075 -> FStar_Pervasives_Native.None)
      | uu____63076 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____63091)::(_typ,uu____63093)::(a1,uu____63095)::(a2,uu____63097)::[]
        ->
        let uu____63118 = eq_t a1 a2  in
        (match uu____63118 with
         | FStar_Syntax_Util.Equal  ->
             let uu____63121 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____63121
         | FStar_Syntax_Util.NotEqual  ->
             let uu____63124 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____63124
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____63127 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____63142)::(_v,uu____63144)::(t1,uu____63146)::(t2,uu____63148)::
        (a1,uu____63150)::(a2,uu____63152)::[] ->
        let uu____63181 =
          let uu____63182 = eq_t t1 t2  in
          let uu____63183 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____63182 uu____63183  in
        (match uu____63181 with
         | FStar_Syntax_Util.Equal  ->
             let uu____63186 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____63186
         | FStar_Syntax_Util.NotEqual  ->
             let uu____63189 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____63189
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____63192 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____63211 =
        let uu____63213 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____63213  in
      failwith uu____63211
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____63229)::[] ->
        let uu____63238 = unembed e_range bogus_cbs a1  in
        (match uu____63238 with
         | FStar_Pervasives_Native.Some r ->
             let uu____63244 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____63244
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____63245 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63281 = arg_as_list e_char a1  in
        (match uu____63281 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63297 = arg_as_string a2  in
             (match uu____63297 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____63310 =
                    let uu____63311 = e_list e_string  in
                    embed uu____63311 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____63310
              | uu____63321 -> FStar_Pervasives_Native.None)
         | uu____63325 -> FStar_Pervasives_Native.None)
    | uu____63331 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63364 =
          let uu____63374 = arg_as_string a1  in
          let uu____63378 = arg_as_int a2  in (uu____63374, uu____63378)  in
        (match uu____63364 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1497_63402  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____63407 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63407) ()
              with | uu___1496_63410 -> FStar_Pervasives_Native.None)
         | uu____63413 -> FStar_Pervasives_Native.None)
    | uu____63423 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63456 =
          let uu____63467 = arg_as_string a1  in
          let uu____63471 = arg_as_char a2  in (uu____63467, uu____63471)  in
        (match uu____63456 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1515_63500  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____63504 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63504) ()
              with | uu___1514_63506 -> FStar_Pervasives_Native.None)
         | uu____63509 -> FStar_Pervasives_Native.None)
    | uu____63520 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____63562 =
          let uu____63576 = arg_as_string a1  in
          let uu____63580 = arg_as_int a2  in
          let uu____63583 = arg_as_int a3  in
          (uu____63576, uu____63580, uu____63583)  in
        (match uu____63562 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1538_63616  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____63621 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63621) ()
              with | uu___1537_63624 -> FStar_Pervasives_Native.None)
         | uu____63627 -> FStar_Pervasives_Native.None)
    | uu____63641 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____63701 =
          let uu____63723 = arg_as_string fn  in
          let uu____63727 = arg_as_int from_line  in
          let uu____63730 = arg_as_int from_col  in
          let uu____63733 = arg_as_int to_line  in
          let uu____63736 = arg_as_int to_col  in
          (uu____63723, uu____63727, uu____63730, uu____63733, uu____63736)
           in
        (match uu____63701 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____63771 =
                 let uu____63772 = FStar_BigInt.to_int_fs from_l  in
                 let uu____63774 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____63772 uu____63774  in
               let uu____63776 =
                 let uu____63777 = FStar_BigInt.to_int_fs to_l  in
                 let uu____63779 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____63777 uu____63779  in
               FStar_Range.mk_range fn1 uu____63771 uu____63776  in
             let uu____63781 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____63781
         | uu____63782 -> FStar_Pervasives_Native.None)
    | uu____63804 -> FStar_Pervasives_Native.None
  
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
                let uu____63894 = FStar_List.splitAt n_tvars args  in
                match uu____63894 with
                | (_tvar_args,rest_args) ->
                    let uu____63943 = FStar_List.hd rest_args  in
                    (match uu____63943 with
                     | (x,uu____63955) ->
                         let uu____63956 = unembed ea cb x  in
                         FStar_Util.map_opt uu____63956
                           (fun x1  ->
                              let uu____63962 = f x1  in
                              embed eb cb uu____63962))
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
                  let uu____64071 = FStar_List.splitAt n_tvars args  in
                  match uu____64071 with
                  | (_tvar_args,rest_args) ->
                      let uu____64120 = FStar_List.hd rest_args  in
                      (match uu____64120 with
                       | (x,uu____64132) ->
                           let uu____64133 =
                             let uu____64138 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____64138  in
                           (match uu____64133 with
                            | (y,uu____64156) ->
                                let uu____64157 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____64157
                                  (fun x1  ->
                                     let uu____64163 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____64163
                                       (fun y1  ->
                                          let uu____64169 =
                                            let uu____64170 = f x1 y1  in
                                            embed ec cb uu____64170  in
                                          FStar_Pervasives_Native.Some
                                            uu____64169))))
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
                    let uu____64298 = FStar_List.splitAt n_tvars args  in
                    match uu____64298 with
                    | (_tvar_args,rest_args) ->
                        let uu____64347 = FStar_List.hd rest_args  in
                        (match uu____64347 with
                         | (x,uu____64359) ->
                             let uu____64360 =
                               let uu____64365 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____64365  in
                             (match uu____64360 with
                              | (y,uu____64383) ->
                                  let uu____64384 =
                                    let uu____64389 =
                                      let uu____64396 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____64396  in
                                    FStar_List.hd uu____64389  in
                                  (match uu____64384 with
                                   | (z,uu____64418) ->
                                       let uu____64419 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____64419
                                         (fun x1  ->
                                            let uu____64425 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____64425
                                              (fun y1  ->
                                                 let uu____64431 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____64431
                                                   (fun z1  ->
                                                      let uu____64437 =
                                                        let uu____64438 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____64438
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____64437))))))
                     in
                  f_wrapped
  