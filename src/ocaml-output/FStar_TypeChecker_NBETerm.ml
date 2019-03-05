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
    match projectee with | Unit  -> true | uu____60744 -> false
  
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____60757 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____60780 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____60805 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____60841 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____60864 -> false
  
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
    match projectee with | Var _0 -> true | uu____61247 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____61284 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____61385 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____61505 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____61569 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____61645 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____61707 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____61727 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____61747 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____61766 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____61798 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____61892 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____61954 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____61978 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____62024 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____62122 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____62256 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____62300 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____62338 -> false
  
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
    match projectee with | TOTAL  -> true | uu____62468 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____62479 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____62490 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____62501 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____62512 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____62523 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____62534 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____62545 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CPS  -> true | uu____62556 -> false
  
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____62568 -> false
  
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
    match trm with | Accu uu____62645 -> true | uu____62657 -> false
  
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with
    | Accu (uu____62667,uu____62668) -> false
    | uu____62682 -> true
  
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
  fun uu___516_62818  ->
    if uu___516_62818
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___517_62829  ->
    if uu___517_62829
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
      | (FStar_Syntax_Util.NotEqual ,uu____62845) ->
          FStar_Syntax_Util.NotEqual
      | (uu____62846,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____62847) -> FStar_Syntax_Util.Unknown
      | (uu____62848,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____62865 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____62885),String (s2,uu____62887)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____62900,uu____62901) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____62937,Lam uu____62938) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____63027 = eq_atom a1 a2  in
          eq_and uu____63027 (fun uu____63029  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____63068 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____63068
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____63084 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____63141  ->
                        match uu____63141 with
                        | ((a1,uu____63155),(a2,uu____63157)) ->
                            let uu____63166 = eq_t a1 a2  in
                            eq_inj acc uu____63166) FStar_Syntax_Util.Equal)
                uu____63084))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____63207 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____63207
          then
            let uu____63210 =
              let uu____63211 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____63211  in
            eq_and uu____63210 (fun uu____63214  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____63221 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____63221
      | (Univ u1,Univ u2) ->
          let uu____63225 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____63225
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____63272 =
            let uu____63273 =
              let uu____63274 = t11 ()  in
              FStar_Pervasives_Native.fst uu____63274  in
            let uu____63279 =
              let uu____63280 = t21 ()  in
              FStar_Pervasives_Native.fst uu____63280  in
            eq_t uu____63273 uu____63279  in
          eq_and uu____63272
            (fun uu____63288  ->
               let uu____63289 =
                 let uu____63290 = mkAccuVar x  in r1 uu____63290  in
               let uu____63291 =
                 let uu____63292 = mkAccuVar x  in r2 uu____63292  in
               eq_t uu____63289 uu____63291)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____63293,uu____63294) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____63299,uu____63300) -> FStar_Syntax_Util.Unknown

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
          let uu____63381 = eq_arg x y  in
          eq_and uu____63381 (fun uu____63383  -> eq_args xs ys)
      | (uu____63384,uu____63385) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____63432) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____63437 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____63437
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____63466) ->
        let uu____63511 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____63522 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____63511 uu____63522
    | Accu (a,l) ->
        let uu____63539 =
          let uu____63541 = atom_to_string a  in
          let uu____63543 =
            let uu____63545 =
              let uu____63547 =
                let uu____63549 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____63549  in
              FStar_String.op_Hat uu____63547 ")"  in
            FStar_String.op_Hat ") (" uu____63545  in
          FStar_String.op_Hat uu____63541 uu____63543  in
        FStar_String.op_Hat "Accu (" uu____63539
    | Construct (fv,us,l) ->
        let uu____63587 =
          let uu____63589 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____63591 =
            let uu____63593 =
              let uu____63595 =
                let uu____63597 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____63597  in
              let uu____63603 =
                let uu____63605 =
                  let uu____63607 =
                    let uu____63609 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____63609  in
                  FStar_String.op_Hat uu____63607 "]"  in
                FStar_String.op_Hat "] [" uu____63605  in
              FStar_String.op_Hat uu____63595 uu____63603  in
            FStar_String.op_Hat ") [" uu____63593  in
          FStar_String.op_Hat uu____63589 uu____63591  in
        FStar_String.op_Hat "Construct (" uu____63587
    | FV (fv,us,l) ->
        let uu____63648 =
          let uu____63650 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____63652 =
            let uu____63654 =
              let uu____63656 =
                let uu____63658 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____63658  in
              let uu____63664 =
                let uu____63666 =
                  let uu____63668 =
                    let uu____63670 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____63670  in
                  FStar_String.op_Hat uu____63668 "]"  in
                FStar_String.op_Hat "] [" uu____63666  in
              FStar_String.op_Hat uu____63656 uu____63664  in
            FStar_String.op_Hat ") [" uu____63654  in
          FStar_String.op_Hat uu____63650 uu____63652  in
        FStar_String.op_Hat "FV (" uu____63648
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____63692 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____63692
    | Type_t u ->
        let uu____63696 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____63696
    | Arrow uu____63699 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____63745 = t ()  in FStar_Pervasives_Native.fst uu____63745
           in
        let uu____63750 =
          let uu____63752 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____63754 =
            let uu____63756 =
              let uu____63758 = t_to_string t1  in
              let uu____63760 =
                let uu____63762 =
                  let uu____63764 =
                    let uu____63766 =
                      let uu____63767 = mkAccuVar x1  in f uu____63767  in
                    t_to_string uu____63766  in
                  FStar_String.op_Hat uu____63764 "}"  in
                FStar_String.op_Hat "{" uu____63762  in
              FStar_String.op_Hat uu____63758 uu____63760  in
            FStar_String.op_Hat ":" uu____63756  in
          FStar_String.op_Hat uu____63752 uu____63754  in
        FStar_String.op_Hat "Refinement " uu____63750
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____63774 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____63774
    | Quote uu____63777 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____63784) ->
        let uu____63801 =
          let uu____63803 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____63803  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____63801
    | Lazy (FStar_Util.Inr (uu____63805,et),uu____63807) ->
        let uu____63824 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____63824
    | Rec
        (uu____63827,uu____63828,l,uu____63830,uu____63831,uu____63832,uu____63833)
        ->
        let uu____63878 =
          let uu____63880 =
            let uu____63882 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____63882  in
          FStar_String.op_Hat uu____63880 ")"  in
        FStar_String.op_Hat "Rec (" uu____63878

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____63893 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____63893
    | Match (t,uu____63897,uu____63898) ->
        let uu____63921 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____63921

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____63925 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____63925 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____63932 =
      FStar_All.pipe_right args (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____63932 (FStar_String.concat " ")

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
        let uu____64403 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____64403 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____64424 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____64424 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____64465  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____64480  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____64523 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____64523
         then
           let uu____64547 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____64547
         else ());
        (let uu____64552 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____64552
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li =
              let uu____64586 = FStar_Dyn.mkdyn x  in (uu____64586, et)  in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____64654 'a .
    'Auu____64654 ->
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
              let uu____64705 = FStar_Common.force_thunk thunk1  in
              f uu____64705
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____64765 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____64765
              then
                let res =
                  let uu____64794 = FStar_Common.force_thunk thunk1  in
                  f uu____64794  in
                ((let uu____64836 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____64836
                  then
                    let uu____64860 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____64862 =
                      FStar_Syntax_Print.emb_typ_to_string et'  in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____64860
                      uu____64862
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____64871 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____64871
                  then
                    let uu____64895 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n"
                      uu____64895
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____64900 ->
              let aopt = f x  in
              ((let uu____64905 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____64905
                then
                  let uu____64929 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n"
                    uu____64929
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
  let uu____64997 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____64997 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____65031 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____65036 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____65031 uu____65036 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____65077 -> FStar_Pervasives_Native.None  in
  let uu____65079 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____65084 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____65079 uu____65084 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____65126 -> FStar_Pervasives_Native.None  in
  let uu____65128 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____65133 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____65128 uu____65133 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____65175)) -> FStar_Pervasives_Native.Some s1
    | uu____65179 -> FStar_Pervasives_Native.None  in
  let uu____65181 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____65186 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____65181 uu____65186 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____65221 -> FStar_Pervasives_Native.None  in
  let uu____65222 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____65227 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____65222 uu____65227 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____65248 =
        let uu____65256 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____65256, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____65248  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____65281  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____65282 =
                 let uu____65283 =
                   let uu____65288 = type_of ea  in as_iarg uu____65288  in
                 [uu____65283]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____65282
           | FStar_Pervasives_Native.Some x ->
               let uu____65298 =
                 let uu____65299 =
                   let uu____65304 = embed ea cb x  in as_arg uu____65304  in
                 let uu____65305 =
                   let uu____65312 =
                     let uu____65317 = type_of ea  in as_iarg uu____65317  in
                   [uu____65312]  in
                 uu____65299 :: uu____65305  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____65298)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____65384)::uu____65385::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____65412 = unembed ea cb a  in
               FStar_Util.bind_opt uu____65412
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____65421 -> FStar_Pervasives_Native.None)
       in
    let uu____65424 =
      let uu____65425 =
        let uu____65426 = let uu____65431 = type_of ea  in as_arg uu____65431
           in
        [uu____65426]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____65425
       in
    mk_emb em un uu____65424 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____65478 =
          let uu____65486 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____65486, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____65478  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____65517  ->
             let uu____65518 =
               let uu____65519 =
                 let uu____65524 =
                   embed eb cb (FStar_Pervasives_Native.snd x)  in
                 as_arg uu____65524  in
               let uu____65525 =
                 let uu____65532 =
                   let uu____65537 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____65537  in
                 let uu____65538 =
                   let uu____65545 =
                     let uu____65550 = type_of eb  in as_iarg uu____65550  in
                   let uu____65551 =
                     let uu____65558 =
                       let uu____65563 = type_of ea  in as_iarg uu____65563
                        in
                     [uu____65558]  in
                   uu____65545 :: uu____65551  in
                 uu____65532 :: uu____65538  in
               uu____65519 :: uu____65525  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____65518)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____65631)::(a,uu____65633)::uu____65634::uu____65635::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____65674 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____65674
                   (fun a1  ->
                      let uu____65684 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____65684
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____65697 -> FStar_Pervasives_Native.None)
         in
      let uu____65702 =
        let uu____65703 =
          let uu____65704 =
            let uu____65709 = type_of eb  in as_arg uu____65709  in
          let uu____65710 =
            let uu____65717 =
              let uu____65722 = type_of ea  in as_arg uu____65722  in
            [uu____65717]  in
          uu____65704 :: uu____65710  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____65703
         in
      mk_emb em un uu____65702 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____65775 =
          let uu____65783 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____65783, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____65775  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____65815  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____65817 =
                   let uu____65818 =
                     let uu____65823 = embed ea cb a  in as_arg uu____65823
                      in
                   let uu____65824 =
                     let uu____65831 =
                       let uu____65836 = type_of eb  in as_iarg uu____65836
                        in
                     let uu____65837 =
                       let uu____65844 =
                         let uu____65849 = type_of ea  in as_iarg uu____65849
                          in
                       [uu____65844]  in
                     uu____65831 :: uu____65837  in
                   uu____65818 :: uu____65824  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____65817
             | FStar_Util.Inr b ->
                 let uu____65867 =
                   let uu____65868 =
                     let uu____65873 = embed eb cb b  in as_arg uu____65873
                      in
                   let uu____65874 =
                     let uu____65881 =
                       let uu____65886 = type_of eb  in as_iarg uu____65886
                        in
                     let uu____65887 =
                       let uu____65894 =
                         let uu____65899 = type_of ea  in as_iarg uu____65899
                          in
                       [uu____65894]  in
                     uu____65881 :: uu____65887  in
                   uu____65868 :: uu____65874  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____65867)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____65961)::uu____65962::uu____65963::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____65998 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____65998
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____66014)::uu____66015::uu____66016::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____66051 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____66051
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____66064 -> FStar_Pervasives_Native.None)
         in
      let uu____66069 =
        let uu____66070 =
          let uu____66071 =
            let uu____66076 = type_of eb  in as_arg uu____66076  in
          let uu____66077 =
            let uu____66084 =
              let uu____66089 = type_of ea  in as_arg uu____66089  in
            [uu____66084]  in
          uu____66071 :: uu____66077  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____66070
         in
      mk_emb em un uu____66069 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____66138 -> FStar_Pervasives_Native.None  in
  let uu____66139 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____66144 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____66139 uu____66144 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____66165 =
        let uu____66173 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____66173, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____66165  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____66200  ->
           let typ = let uu____66202 = type_of ea  in as_iarg uu____66202  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____66223 =
               let uu____66224 = as_arg tl1  in
               let uu____66229 =
                 let uu____66236 =
                   let uu____66241 = embed ea cb hd1  in as_arg uu____66241
                    in
                 [uu____66236; typ]  in
               uu____66224 :: uu____66229  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____66223
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____66289,uu____66290) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____66310,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____66313,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____66314))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____66342 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____66342
                 (fun hd2  ->
                    let uu____66350 = un cb tl1  in
                    FStar_Util.bind_opt uu____66350
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____66366,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____66391 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____66391
                 (fun hd2  ->
                    let uu____66399 = un cb tl1  in
                    FStar_Util.bind_opt uu____66399
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____66414 -> FStar_Pervasives_Native.None)
       in
    let uu____66417 =
      let uu____66418 =
        let uu____66419 = let uu____66424 = type_of ea  in as_arg uu____66424
           in
        [uu____66419]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____66418
       in
    mk_emb em un uu____66417 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____66497  ->
             Lam
               ((fun tas  ->
                   let uu____66527 =
                     let uu____66530 = FStar_List.hd tas  in
                     unembed ea cb uu____66530  in
                   match uu____66527 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____66532 = f a  in embed eb cb uu____66532
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____66545  ->
                     let uu____66548 = type_of eb  in as_arg uu____66548)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____66606 =
                 let uu____66609 =
                   let uu____66610 =
                     let uu____66611 =
                       let uu____66616 = embed ea cb x  in as_arg uu____66616
                        in
                     [uu____66611]  in
                   cb.iapp lam1 uu____66610  in
                 unembed eb cb uu____66609  in
               match uu____66606 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____66630 =
        let uu____66631 = type_of ea  in
        let uu____66632 =
          let uu____66633 = type_of eb  in as_iarg uu____66633  in
        make_arrow1 uu____66631 uu____66632  in
      mk_emb em un uu____66630 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____66651 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66651 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____66656 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66656 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____66661 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66661 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____66666 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66666 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____66671 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66671 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____66676 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66676 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____66681 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66681 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____66686 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66686 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____66691 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____66691 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____66700 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66701 =
          let uu____66702 =
            let uu____66707 =
              let uu____66708 = e_list e_string  in embed uu____66708 cb l
               in
            as_arg uu____66707  in
          [uu____66702]  in
        mkFV uu____66700 [] uu____66701
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____66730 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66731 =
          let uu____66732 =
            let uu____66737 =
              let uu____66738 = e_list e_string  in embed uu____66738 cb l
               in
            as_arg uu____66737  in
          [uu____66732]  in
        mkFV uu____66730 [] uu____66731
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____66760 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____66761 =
          let uu____66762 =
            let uu____66767 =
              let uu____66768 = e_list e_string  in embed uu____66768 cb l
               in
            as_arg uu____66767  in
          [uu____66762]  in
        mkFV uu____66760 [] uu____66761
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____66802,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____66818,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____66834,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____66850,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____66866,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____66882,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____66898,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____66914,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____66930,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____66946,(l,uu____66948)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____66967 =
          let uu____66973 = e_list e_string  in unembed uu____66973 cb l  in
        FStar_Util.bind_opt uu____66967
          (fun ss  ->
             FStar_All.pipe_left
               (fun _66993  -> FStar_Pervasives_Native.Some _66993)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____66995,(l,uu____66997)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____67016 =
          let uu____67022 = e_list e_string  in unembed uu____67022 cb l  in
        FStar_Util.bind_opt uu____67016
          (fun ss  ->
             FStar_All.pipe_left
               (fun _67042  -> FStar_Pervasives_Native.Some _67042)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____67044,(l,uu____67046)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____67065 =
          let uu____67071 = e_list e_string  in unembed uu____67071 cb l  in
        FStar_Util.bind_opt uu____67065
          (fun ss  ->
             FStar_All.pipe_left
               (fun _67091  -> FStar_Pervasives_Native.Some _67091)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____67092 ->
        ((let uu____67094 =
            let uu____67100 =
              let uu____67102 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____67102
               in
            (FStar_Errors.Warning_NotEmbedded, uu____67100)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____67094);
         FStar_Pervasives_Native.None)
     in
  let uu____67106 =
    let uu____67107 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____67107 [] []  in
  let uu____67112 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____67106 uu____67112 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____67121  -> failwith "bogus_cbs translate")
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
      let uu____67198 =
        let uu____67207 = e_list e  in unembed uu____67207 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____67198
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____67229  ->
    match uu____67229 with
    | (a,uu____67237) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____67252)::[]) when
             let uu____67269 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____67269 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____67276 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____67319 = let uu____67326 = as_arg c  in [uu____67326]  in
      int_to_t2 uu____67319
  
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
          let uu____67380 = f a  in FStar_Pervasives_Native.Some uu____67380
      | uu____67381 -> FStar_Pervasives_Native.None
  
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
          let uu____67435 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____67435
      | uu____67436 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____67480 = FStar_List.map as_a args  in
        lift_unary f uu____67480
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____67535 = FStar_List.map as_a args  in
        lift_binary f uu____67535
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____67565 = f x  in embed e_int bogus_cbs uu____67565)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____67592 = f x y  in embed e_int bogus_cbs uu____67592)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____67618 = f x  in embed e_bool bogus_cbs uu____67618)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____67656 = f x y  in embed e_bool bogus_cbs uu____67656)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____67694 = f x y  in embed e_string bogus_cbs uu____67694)
  
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
                let uu____67799 =
                  let uu____67808 = as_a a  in
                  let uu____67811 = as_b b  in (uu____67808, uu____67811)  in
                (match uu____67799 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____67826 =
                       let uu____67827 = f a1 b1  in embed_c uu____67827  in
                     FStar_Pervasives_Native.Some uu____67826
                 | uu____67828 -> FStar_Pervasives_Native.None)
            | uu____67837 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____67846 = e_list e_char  in
    let uu____67853 = FStar_String.list_of_string s  in
    embed uu____67846 bogus_cbs uu____67853
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____67892 =
        let uu____67893 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____67893  in
      embed e_int bogus_cbs uu____67892
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____67927 = arg_as_string a1  in
        (match uu____67927 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____67936 = arg_as_list e_string a2  in
             (match uu____67936 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____67954 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____67954
              | uu____67956 -> FStar_Pervasives_Native.None)
         | uu____67962 -> FStar_Pervasives_Native.None)
    | uu____67966 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____67973 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____67973
  
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
      | (_typ,uu____68035)::(a1,uu____68037)::(a2,uu____68039)::[] ->
          let uu____68056 = eq_t a1 a2  in
          (match uu____68056 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____68065 -> FStar_Pervasives_Native.None)
      | uu____68066 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____68081)::(_typ,uu____68083)::(a1,uu____68085)::(a2,uu____68087)::[]
        ->
        let uu____68108 = eq_t a1 a2  in
        (match uu____68108 with
         | FStar_Syntax_Util.Equal  ->
             let uu____68111 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____68111
         | FStar_Syntax_Util.NotEqual  ->
             let uu____68114 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____68114
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____68117 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____68132)::(_v,uu____68134)::(t1,uu____68136)::(t2,uu____68138)::
        (a1,uu____68140)::(a2,uu____68142)::[] ->
        let uu____68171 =
          let uu____68172 = eq_t t1 t2  in
          let uu____68173 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____68172 uu____68173  in
        (match uu____68171 with
         | FStar_Syntax_Util.Equal  ->
             let uu____68176 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____68176
         | FStar_Syntax_Util.NotEqual  ->
             let uu____68179 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____68179
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____68182 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____68201 =
        let uu____68203 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____68203  in
      failwith uu____68201
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____68219)::[] ->
        let uu____68228 = unembed e_range bogus_cbs a1  in
        (match uu____68228 with
         | FStar_Pervasives_Native.Some r ->
             let uu____68234 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____68234
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____68235 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68271 = arg_as_list e_char a1  in
        (match uu____68271 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____68287 = arg_as_string a2  in
             (match uu____68287 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____68300 =
                    let uu____68301 = e_list e_string  in
                    embed uu____68301 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____68300
              | uu____68311 -> FStar_Pervasives_Native.None)
         | uu____68315 -> FStar_Pervasives_Native.None)
    | uu____68321 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68354 =
          let uu____68364 = arg_as_string a1  in
          let uu____68368 = arg_as_int a2  in (uu____68364, uu____68368)  in
        (match uu____68354 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1497_68392  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____68397 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68397) ()
              with | uu___1496_68400 -> FStar_Pervasives_Native.None)
         | uu____68403 -> FStar_Pervasives_Native.None)
    | uu____68413 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____68446 =
          let uu____68457 = arg_as_string a1  in
          let uu____68461 = arg_as_char a2  in (uu____68457, uu____68461)  in
        (match uu____68446 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1515_68490  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____68494 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68494) ()
              with | uu___1514_68496 -> FStar_Pervasives_Native.None)
         | uu____68499 -> FStar_Pervasives_Native.None)
    | uu____68510 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____68552 =
          let uu____68566 = arg_as_string a1  in
          let uu____68570 = arg_as_int a2  in
          let uu____68573 = arg_as_int a3  in
          (uu____68566, uu____68570, uu____68573)  in
        (match uu____68552 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1538_68606  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____68611 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____68611) ()
              with | uu___1537_68614 -> FStar_Pervasives_Native.None)
         | uu____68617 -> FStar_Pervasives_Native.None)
    | uu____68631 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____68691 =
          let uu____68713 = arg_as_string fn  in
          let uu____68717 = arg_as_int from_line  in
          let uu____68720 = arg_as_int from_col  in
          let uu____68723 = arg_as_int to_line  in
          let uu____68726 = arg_as_int to_col  in
          (uu____68713, uu____68717, uu____68720, uu____68723, uu____68726)
           in
        (match uu____68691 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____68761 =
                 let uu____68762 = FStar_BigInt.to_int_fs from_l  in
                 let uu____68764 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____68762 uu____68764  in
               let uu____68766 =
                 let uu____68767 = FStar_BigInt.to_int_fs to_l  in
                 let uu____68769 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____68767 uu____68769  in
               FStar_Range.mk_range fn1 uu____68761 uu____68766  in
             let uu____68771 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____68771
         | uu____68772 -> FStar_Pervasives_Native.None)
    | uu____68794 -> FStar_Pervasives_Native.None
  
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
                let uu____68884 = FStar_List.splitAt n_tvars args  in
                match uu____68884 with
                | (_tvar_args,rest_args) ->
                    let uu____68933 = FStar_List.hd rest_args  in
                    (match uu____68933 with
                     | (x,uu____68945) ->
                         let uu____68946 = unembed ea cb x  in
                         FStar_Util.map_opt uu____68946
                           (fun x1  ->
                              let uu____68952 = f x1  in
                              embed eb cb uu____68952))
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
                  let uu____69061 = FStar_List.splitAt n_tvars args  in
                  match uu____69061 with
                  | (_tvar_args,rest_args) ->
                      let uu____69110 = FStar_List.hd rest_args  in
                      (match uu____69110 with
                       | (x,uu____69122) ->
                           let uu____69123 =
                             let uu____69128 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____69128  in
                           (match uu____69123 with
                            | (y,uu____69146) ->
                                let uu____69147 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____69147
                                  (fun x1  ->
                                     let uu____69153 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____69153
                                       (fun y1  ->
                                          let uu____69159 =
                                            let uu____69160 = f x1 y1  in
                                            embed ec cb uu____69160  in
                                          FStar_Pervasives_Native.Some
                                            uu____69159))))
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
                    let uu____69288 = FStar_List.splitAt n_tvars args  in
                    match uu____69288 with
                    | (_tvar_args,rest_args) ->
                        let uu____69337 = FStar_List.hd rest_args  in
                        (match uu____69337 with
                         | (x,uu____69349) ->
                             let uu____69350 =
                               let uu____69355 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____69355  in
                             (match uu____69350 with
                              | (y,uu____69373) ->
                                  let uu____69374 =
                                    let uu____69379 =
                                      let uu____69386 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____69386  in
                                    FStar_List.hd uu____69379  in
                                  (match uu____69374 with
                                   | (z,uu____69408) ->
                                       let uu____69409 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____69409
                                         (fun x1  ->
                                            let uu____69415 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____69415
                                              (fun y1  ->
                                                 let uu____69421 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____69421
                                                   (fun z1  ->
                                                      let uu____69427 =
                                                        let uu____69428 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____69428
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____69427))))))
                     in
                  f_wrapped
  