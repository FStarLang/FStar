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
    match projectee with | Unit  -> true | uu____55899 -> false
  
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____55912 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Int _0 -> true | uu____55934 -> false
  
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____55958 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____55993 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____56015 -> false
  
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
    match projectee with | Var _0 -> true | uu____56397 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____56433 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t * (t -> t) *
      ((t -> FStar_Syntax_Syntax.term) ->
         FStar_Syntax_Syntax.branch Prims.list)))
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____56533 -> false
  
let (__proj__Lam__item___0 :
  t ->
    ((t Prims.list -> t) * (t Prims.list -> (t * FStar_Syntax_Syntax.aqual))
      Prims.list * Prims.int * (unit -> residual_comp)
      FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____56652 -> false
  
let (__proj__Accu__item___0 :
  t -> (atom * (t * FStar_Syntax_Syntax.aqual) Prims.list)) =
  fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____56715 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | FV _0 -> true | uu____56790 -> false
  
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv * FStar_Syntax_Syntax.universe Prims.list * (t *
      FStar_Syntax_Syntax.aqual) Prims.list))
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____56851 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____56870 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____56889 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____56907 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____56939 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    ((t Prims.list -> comp) *
      (t Prims.list -> (t * FStar_Syntax_Syntax.aqual)) Prims.list))
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____57032 -> false
  
let (__proj__Refinement__item___0 :
  t -> ((t -> t) * (unit -> (t * FStar_Syntax_Syntax.aqual)))) =
  fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Reflect : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Reflect _0 -> true | uu____57093 -> false
  
let (__proj__Reflect__item___0 : t -> t) =
  fun projectee  -> match projectee with | Reflect _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____57116 -> false
  
let (__proj__Quote__item___0 :
  t -> (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.quoteinfo)) =
  fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____57161 -> false
  
let (__proj__Lazy__item___0 :
  t ->
    ((FStar_Syntax_Syntax.lazyinfo,(FStar_Dyn.dyn *
                                     FStar_Syntax_Syntax.emb_typ))
      FStar_Util.either * t FStar_Common.thunk))
  = fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____57258 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding * FStar_Syntax_Syntax.letbinding
      Prims.list * t Prims.list * (t * FStar_Syntax_Syntax.aqual) Prims.list
      * Prims.int * Prims.bool Prims.list *
      (t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)))
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____57391 -> false
  
let (__proj__Tot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____57434 -> false
  
let (__proj__GTot__item___0 :
  comp -> (t * FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option))
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____57471 -> false
  
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
    match projectee with | TOTAL  -> true | uu____57600 -> false
  
let (uu___is_MLEFFECT : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | MLEFFECT  -> true | uu____57611 -> false
  
let (uu___is_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | RETURN  -> true | uu____57622 -> false
  
let (uu___is_PARTIAL_RETURN : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | PARTIAL_RETURN  -> true | uu____57633 -> false
  
let (uu___is_SOMETRIVIAL : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SOMETRIVIAL  -> true | uu____57644 -> false
  
let (uu___is_TRIVIAL_POSTCONDITION : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | TRIVIAL_POSTCONDITION  -> true
    | uu____57655 -> false
  
let (uu___is_SHOULD_NOT_INLINE : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | SHOULD_NOT_INLINE  -> true | uu____57666 -> false
  
let (uu___is_LEMMA : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | LEMMA  -> true | uu____57677 -> false
  
let (uu___is_CPS : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | CPS  -> true | uu____57688 -> false
  
let (uu___is_DECREASES : cflag -> Prims.bool) =
  fun projectee  ->
    match projectee with | DECREASES _0 -> true | uu____57700 -> false
  
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
    match trm with | Accu uu____57776 -> true | uu____57788 -> false
  
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with
    | Accu (uu____57798,uu____57799) -> false
    | uu____57813 -> true
  
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
  fun uu___516_57949  ->
    if uu___516_57949
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___517_57960  ->
    if uu___517_57960
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
      | (FStar_Syntax_Util.NotEqual ,uu____57976) ->
          FStar_Syntax_Util.NotEqual
      | (uu____57977,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____57978) -> FStar_Syntax_Util.Unknown
      | (uu____57979,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____57996 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____58016),String (s2,uu____58018)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____58031,uu____58032) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____58068,Lam uu____58069) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____58158 = eq_atom a1 a2  in
          eq_and uu____58158 (fun uu____58160  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____58199 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____58199
          then
            (if (FStar_List.length args1) <> (FStar_List.length args2)
             then failwith "eq_t, different number of args on Construct"
             else ();
             (let uu____58215 = FStar_List.zip args1 args2  in
              FStar_All.pipe_left
                (FStar_List.fold_left
                   (fun acc  ->
                      fun uu____58272  ->
                        match uu____58272 with
                        | ((a1,uu____58286),(a2,uu____58288)) ->
                            let uu____58297 = eq_t a1 a2  in
                            eq_inj acc uu____58297) FStar_Syntax_Util.Equal)
                uu____58215))
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____58338 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____58338
          then
            let uu____58341 =
              let uu____58342 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____58342  in
            eq_and uu____58341 (fun uu____58345  -> eq_args args1 args2)
          else FStar_Syntax_Util.Unknown
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____58352 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____58352
      | (Univ u1,Univ u2) ->
          let uu____58356 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____58356
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____58403 =
            let uu____58404 =
              let uu____58405 = t11 ()  in
              FStar_Pervasives_Native.fst uu____58405  in
            let uu____58410 =
              let uu____58411 = t21 ()  in
              FStar_Pervasives_Native.fst uu____58411  in
            eq_t uu____58404 uu____58410  in
          eq_and uu____58403
            (fun uu____58419  ->
               let uu____58420 =
                 let uu____58421 = mkAccuVar x  in r1 uu____58421  in
               let uu____58422 =
                 let uu____58423 = mkAccuVar x  in r2 uu____58423  in
               eq_t uu____58420 uu____58422)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____58424,uu____58425) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____58430,uu____58431) -> FStar_Syntax_Util.Unknown

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
          let uu____58512 = eq_arg x y  in
          eq_and uu____58512 (fun uu____58514  -> eq_args xs ys)
      | (uu____58515,uu____58516) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____58563) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____58568 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____58568
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity,uu____58597) ->
        let uu____58642 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____58653 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____58642 uu____58653
    | Accu (a,l) ->
        let uu____58670 =
          let uu____58672 = atom_to_string a  in
          let uu____58674 =
            let uu____58676 =
              let uu____58678 =
                let uu____58680 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____58680  in
              FStar_String.op_Hat uu____58678 ")"  in
            FStar_String.op_Hat ") (" uu____58676  in
          FStar_String.op_Hat uu____58672 uu____58674  in
        FStar_String.op_Hat "Accu (" uu____58670
    | Construct (fv,us,l) ->
        let uu____58718 =
          let uu____58720 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____58722 =
            let uu____58724 =
              let uu____58726 =
                let uu____58728 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____58728  in
              let uu____58734 =
                let uu____58736 =
                  let uu____58738 =
                    let uu____58740 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____58740  in
                  FStar_String.op_Hat uu____58738 "]"  in
                FStar_String.op_Hat "] [" uu____58736  in
              FStar_String.op_Hat uu____58726 uu____58734  in
            FStar_String.op_Hat ") [" uu____58724  in
          FStar_String.op_Hat uu____58720 uu____58722  in
        FStar_String.op_Hat "Construct (" uu____58718
    | FV (fv,us,l) ->
        let uu____58779 =
          let uu____58781 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____58783 =
            let uu____58785 =
              let uu____58787 =
                let uu____58789 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____58789  in
              let uu____58795 =
                let uu____58797 =
                  let uu____58799 =
                    let uu____58801 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____58801  in
                  FStar_String.op_Hat uu____58799 "]"  in
                FStar_String.op_Hat "] [" uu____58797  in
              FStar_String.op_Hat uu____58787 uu____58795  in
            FStar_String.op_Hat ") [" uu____58785  in
          FStar_String.op_Hat uu____58781 uu____58783  in
        FStar_String.op_Hat "FV (" uu____58779
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____58823 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Universe " uu____58823
    | Type_t u ->
        let uu____58827 = FStar_Syntax_Print.univ_to_string u  in
        FStar_String.op_Hat "Type_t " uu____58827
    | Arrow uu____58830 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____58876 = t ()  in FStar_Pervasives_Native.fst uu____58876
           in
        let uu____58881 =
          let uu____58883 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____58885 =
            let uu____58887 =
              let uu____58889 = t_to_string t1  in
              let uu____58891 =
                let uu____58893 =
                  let uu____58895 =
                    let uu____58897 =
                      let uu____58898 = mkAccuVar x1  in f uu____58898  in
                    t_to_string uu____58897  in
                  FStar_String.op_Hat uu____58895 "}"  in
                FStar_String.op_Hat "{" uu____58893  in
              FStar_String.op_Hat uu____58889 uu____58891  in
            FStar_String.op_Hat ":" uu____58887  in
          FStar_String.op_Hat uu____58883 uu____58885  in
        FStar_String.op_Hat "Refinement " uu____58881
    | Unknown  -> "Unknown"
    | Reflect t ->
        let uu____58905 = t_to_string t  in
        FStar_String.op_Hat "Reflect " uu____58905
    | Quote uu____58908 -> "Quote _"
    | Lazy (FStar_Util.Inl li,uu____58915) ->
        let uu____58932 =
          let uu____58934 = FStar_Syntax_Util.unfold_lazy li  in
          FStar_Syntax_Print.term_to_string uu____58934  in
        FStar_Util.format1 "Lazy (Inl {%s})" uu____58932
    | Lazy (FStar_Util.Inr (uu____58936,et),uu____58938) ->
        let uu____58955 = FStar_Syntax_Print.emb_typ_to_string et  in
        FStar_Util.format1 "Lazy (Inr (?, %s))" uu____58955
    | Rec
        (uu____58958,uu____58959,l,uu____58961,uu____58962,uu____58963,uu____58964)
        ->
        let uu____59009 =
          let uu____59011 =
            let uu____59013 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____59013  in
          FStar_String.op_Hat uu____59011 ")"  in
        FStar_String.op_Hat "Rec (" uu____59009

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____59024 = FStar_Syntax_Print.bv_to_string v1  in
        FStar_String.op_Hat "Var " uu____59024
    | Match (t,uu____59028,uu____59029) ->
        let uu____59052 = t_to_string t  in
        FStar_String.op_Hat "Match " uu____59052

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____59056 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____59056 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____59063 =
      FStar_All.pipe_right args (FStar_List.map arg_to_string)  in
    FStar_All.pipe_right uu____59063 (FStar_String.concat " ")

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
        let uu____59534 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____59534 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____59555 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkFV uu____59555 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____59596  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____59611  -> a)])
  
let lazy_embed : 'a . FStar_Syntax_Syntax.emb_typ -> 'a -> (unit -> t) -> t =
  fun et  ->
    fun x  ->
      fun f  ->
        (let uu____59654 = FStar_ST.op_Bang FStar_Options.debug_embedding  in
         if uu____59654
         then
           let uu____59678 = FStar_Syntax_Print.emb_typ_to_string et  in
           FStar_Util.print1 "Embedding\n\temb_typ=%s\n" uu____59678
         else ());
        (let uu____59683 = FStar_ST.op_Bang FStar_Options.eager_embedding  in
         if uu____59683
         then f ()
         else
           (let thunk1 = FStar_Common.mk_thunk f  in
            let li =
              let uu____59717 = FStar_Dyn.mkdyn x  in (uu____59717, et)  in
            Lazy ((FStar_Util.Inr li), thunk1)))
  
let lazy_unembed :
  'Auu____59745 'a .
    'Auu____59745 ->
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
              let uu____59796 = FStar_Common.force_thunk thunk1  in
              f uu____59796
          | Lazy (FStar_Util.Inr (b,et'),thunk1) ->
              let uu____59816 =
                (et <> et') ||
                  (FStar_ST.op_Bang FStar_Options.eager_embedding)
                 in
              if uu____59816
              then
                let res =
                  let uu____59845 = FStar_Common.force_thunk thunk1  in
                  f uu____59845  in
                ((let uu____59847 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____59847
                  then
                    let uu____59871 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    let uu____59873 =
                      FStar_Syntax_Print.emb_typ_to_string et'  in
                    FStar_Util.print2
                      "Unembed cancellation failed\n\t%s <> %s\n" uu____59871
                      uu____59873
                  else ());
                 res)
              else
                (let a = FStar_Dyn.undyn b  in
                 (let uu____59882 =
                    FStar_ST.op_Bang FStar_Options.debug_embedding  in
                  if uu____59882
                  then
                    let uu____59906 = FStar_Syntax_Print.emb_typ_to_string et
                       in
                    FStar_Util.print1 "Unembed cancelled for %s\n"
                      uu____59906
                  else ());
                 FStar_Pervasives_Native.Some a)
          | uu____59911 ->
              let aopt = f x  in
              ((let uu____59916 =
                  FStar_ST.op_Bang FStar_Options.debug_embedding  in
                if uu____59916
                then
                  let uu____59940 = FStar_Syntax_Print.emb_typ_to_string et
                     in
                  FStar_Util.print1 "Unembedding:\n\temb_typ=%s\n"
                    uu____59940
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
  let uu____60008 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____60008 FStar_Syntax_Syntax.ET_abstract 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____60042 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  let uu____60047 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____60042 uu____60047 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____60088 -> FStar_Pervasives_Native.None  in
  let uu____60090 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  let uu____60095 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_unit  in
  mk_emb em un uu____60090 uu____60095 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____60137 -> FStar_Pervasives_Native.None  in
  let uu____60139 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  let uu____60144 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_char  in
  mk_emb em un uu____60139 uu____60144 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____60186)) -> FStar_Pervasives_Native.Some s1
    | uu____60190 -> FStar_Pervasives_Native.None  in
  let uu____60192 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  let uu____60197 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_string  in
  mk_emb em un uu____60192 uu____60197 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____60232 -> FStar_Pervasives_Native.None  in
  let uu____60233 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  let uu____60238 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_int  in
  mk_emb em un uu____60233 uu____60238 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let etyp =
      let uu____60259 =
        let uu____60267 =
          FStar_All.pipe_right FStar_Parser_Const.option_lid
            FStar_Ident.string_of_lid
           in
        (uu____60267, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____60259  in
    let em cb o =
      lazy_embed etyp o
        (fun uu____60292  ->
           match o with
           | FStar_Pervasives_Native.None  ->
               let uu____60293 =
                 let uu____60294 =
                   let uu____60299 = type_of ea  in as_iarg uu____60299  in
                 [uu____60294]  in
               lid_as_constr FStar_Parser_Const.none_lid
                 [FStar_Syntax_Syntax.U_zero] uu____60293
           | FStar_Pervasives_Native.Some x ->
               let uu____60309 =
                 let uu____60310 =
                   let uu____60315 = embed ea cb x  in as_arg uu____60315  in
                 let uu____60316 =
                   let uu____60323 =
                     let uu____60328 = type_of ea  in as_iarg uu____60328  in
                   [uu____60323]  in
                 uu____60310 :: uu____60316  in
               lid_as_constr FStar_Parser_Const.some_lid
                 [FStar_Syntax_Syntax.U_zero] uu____60309)
       in
    let un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fvar1,us,args) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.none_lid
               -> FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
           | Construct (fvar1,us,(a,uu____60395)::uu____60396::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fvar1
                 FStar_Parser_Const.some_lid
               ->
               let uu____60423 = unembed ea cb a  in
               FStar_Util.bind_opt uu____60423
                 (fun a1  ->
                    FStar_Pervasives_Native.Some
                      (FStar_Pervasives_Native.Some a1))
           | uu____60432 -> FStar_Pervasives_Native.None)
       in
    let uu____60435 =
      let uu____60436 =
        let uu____60437 = let uu____60442 = type_of ea  in as_arg uu____60442
           in
        [uu____60437]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____60436
       in
    mk_emb em un uu____60435 etyp
  
let e_tuple2 : 'a 'b . 'a embedding -> 'b embedding -> ('a * 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____60489 =
          let uu____60497 =
            FStar_All.pipe_right FStar_Parser_Const.lid_tuple2
              FStar_Ident.string_of_lid
             in
          (uu____60497, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60489  in
      let em cb x =
        lazy_embed etyp x
          (fun uu____60528  ->
             let uu____60529 =
               let uu____60530 =
                 let uu____60535 =
                   embed eb cb (FStar_Pervasives_Native.snd x)  in
                 as_arg uu____60535  in
               let uu____60536 =
                 let uu____60543 =
                   let uu____60548 =
                     embed ea cb (FStar_Pervasives_Native.fst x)  in
                   as_arg uu____60548  in
                 let uu____60549 =
                   let uu____60556 =
                     let uu____60561 = type_of eb  in as_iarg uu____60561  in
                   let uu____60562 =
                     let uu____60569 =
                       let uu____60574 = type_of ea  in as_iarg uu____60574
                        in
                     [uu____60569]  in
                   uu____60556 :: uu____60562  in
                 uu____60543 :: uu____60549  in
               uu____60530 :: uu____60536  in
             lid_as_constr FStar_Parser_Const.lid_Mktuple2
               [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
               uu____60529)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(b,uu____60642)::(a,uu____60644)::uu____60645::uu____60646::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.lid_Mktuple2
                 ->
                 let uu____60685 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____60685
                   (fun a1  ->
                      let uu____60695 = unembed eb cb b  in
                      FStar_Util.bind_opt uu____60695
                        (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
             | uu____60708 -> FStar_Pervasives_Native.None)
         in
      let uu____60713 =
        let uu____60714 =
          let uu____60715 =
            let uu____60720 = type_of eb  in as_arg uu____60720  in
          let uu____60721 =
            let uu____60728 =
              let uu____60733 = type_of ea  in as_arg uu____60733  in
            [uu____60728]  in
          uu____60715 :: uu____60721  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____60714
         in
      mk_emb em un uu____60713 etyp
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let etyp =
        let uu____60786 =
          let uu____60794 =
            FStar_All.pipe_right FStar_Parser_Const.either_lid
              FStar_Ident.string_of_lid
             in
          (uu____60794, [ea.emb_typ; eb.emb_typ])  in
        FStar_Syntax_Syntax.ET_app uu____60786  in
      let em cb s =
        lazy_embed etyp s
          (fun uu____60826  ->
             match s with
             | FStar_Util.Inl a ->
                 let uu____60828 =
                   let uu____60829 =
                     let uu____60834 = embed ea cb a  in as_arg uu____60834
                      in
                   let uu____60835 =
                     let uu____60842 =
                       let uu____60847 = type_of eb  in as_iarg uu____60847
                        in
                     let uu____60848 =
                       let uu____60855 =
                         let uu____60860 = type_of ea  in as_iarg uu____60860
                          in
                       [uu____60855]  in
                     uu____60842 :: uu____60848  in
                   uu____60829 :: uu____60835  in
                 lid_as_constr FStar_Parser_Const.inl_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____60828
             | FStar_Util.Inr b ->
                 let uu____60878 =
                   let uu____60879 =
                     let uu____60884 = embed eb cb b  in as_arg uu____60884
                      in
                   let uu____60885 =
                     let uu____60892 =
                       let uu____60897 = type_of eb  in as_iarg uu____60897
                        in
                     let uu____60898 =
                       let uu____60905 =
                         let uu____60910 = type_of ea  in as_iarg uu____60910
                          in
                       [uu____60905]  in
                     uu____60892 :: uu____60898  in
                   uu____60879 :: uu____60885  in
                 lid_as_constr FStar_Parser_Const.inr_lid
                   [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
                   uu____60878)
         in
      let un cb trm =
        lazy_unembed cb etyp trm
          (fun trm1  ->
             match trm1 with
             | Construct
                 (fvar1,us,(a,uu____60972)::uu____60973::uu____60974::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inl_lid
                 ->
                 let uu____61009 = unembed ea cb a  in
                 FStar_Util.bind_opt uu____61009
                   (fun a1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
             | Construct
                 (fvar1,us,(b,uu____61025)::uu____61026::uu____61027::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fvar1
                   FStar_Parser_Const.inr_lid
                 ->
                 let uu____61062 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____61062
                   (fun b1  ->
                      FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
             | uu____61075 -> FStar_Pervasives_Native.None)
         in
      let uu____61080 =
        let uu____61081 =
          let uu____61082 =
            let uu____61087 = type_of eb  in as_arg uu____61087  in
          let uu____61088 =
            let uu____61095 =
              let uu____61100 = type_of ea  in as_arg uu____61100  in
            [uu____61095]  in
          uu____61082 :: uu____61088  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
          uu____61081
         in
      mk_emb em un uu____61080 etyp
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____61149 -> FStar_Pervasives_Native.None  in
  let uu____61150 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  let uu____61155 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_range  in
  mk_emb em un uu____61150 uu____61155 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let etyp =
      let uu____61176 =
        let uu____61184 =
          FStar_All.pipe_right FStar_Parser_Const.list_lid
            FStar_Ident.string_of_lid
           in
        (uu____61184, [ea.emb_typ])  in
      FStar_Syntax_Syntax.ET_app uu____61176  in
    let em cb l =
      lazy_embed etyp l
        (fun uu____61211  ->
           let typ = let uu____61213 = type_of ea  in as_iarg uu____61213  in
           let nil =
             lid_as_constr FStar_Parser_Const.nil_lid
               [FStar_Syntax_Syntax.U_zero] [typ]
              in
           let cons1 hd1 tl1 =
             let uu____61234 =
               let uu____61235 = as_arg tl1  in
               let uu____61240 =
                 let uu____61247 =
                   let uu____61252 = embed ea cb hd1  in as_arg uu____61252
                    in
                 [uu____61247; typ]  in
               uu____61235 :: uu____61240  in
             lid_as_constr FStar_Parser_Const.cons_lid
               [FStar_Syntax_Syntax.U_zero] uu____61234
              in
           FStar_List.fold_right cons1 l nil)
       in
    let rec un cb trm =
      lazy_unembed cb etyp trm
        (fun trm1  ->
           match trm1 with
           | Construct (fv,uu____61300,uu____61301) when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
               FStar_Pervasives_Native.Some []
           | Construct
               (fv,uu____61321,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::
                (uu____61324,FStar_Pervasives_Native.Some
                 (FStar_Syntax_Syntax.Implicit uu____61325))::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____61353 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____61353
                 (fun hd2  ->
                    let uu____61361 = un cb tl1  in
                    FStar_Util.bind_opt uu____61361
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | Construct
               (fv,uu____61377,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                                    )::[])
               when
               FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
               ->
               let uu____61402 = unembed ea cb hd1  in
               FStar_Util.bind_opt uu____61402
                 (fun hd2  ->
                    let uu____61410 = un cb tl1  in
                    FStar_Util.bind_opt uu____61410
                      (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
           | uu____61425 -> FStar_Pervasives_Native.None)
       in
    let uu____61428 =
      let uu____61429 =
        let uu____61430 = let uu____61435 = type_of ea  in as_arg uu____61435
           in
        [uu____61430]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____61429
       in
    mk_emb em un uu____61428 etyp
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let etyp = FStar_Syntax_Syntax.ET_fun ((ea.emb_typ), (eb.emb_typ))  in
      let em cb f =
        lazy_embed etyp f
          (fun uu____61508  ->
             Lam
               ((fun tas  ->
                   let uu____61538 =
                     let uu____61541 = FStar_List.hd tas  in
                     unembed ea cb uu____61541  in
                   match uu____61538 with
                   | FStar_Pervasives_Native.Some a ->
                       let uu____61543 = f a  in embed eb cb uu____61543
                   | FStar_Pervasives_Native.None  ->
                       failwith "cannot unembed function argument"),
                 [(fun uu____61556  ->
                     let uu____61559 = type_of eb  in as_arg uu____61559)],
                 (Prims.parse_int "1"), FStar_Pervasives_Native.None))
         in
      let un cb lam =
        let k lam1 =
          FStar_Pervasives_Native.Some
            (fun x  ->
               let uu____61617 =
                 let uu____61620 =
                   let uu____61621 =
                     let uu____61622 =
                       let uu____61627 = embed ea cb x  in as_arg uu____61627
                        in
                     [uu____61622]  in
                   cb.iapp lam1 uu____61621  in
                 unembed eb cb uu____61620  in
               match uu____61617 with
               | FStar_Pervasives_Native.Some y -> y
               | FStar_Pervasives_Native.None  ->
                   failwith "cannot unembed function result")
           in
        lazy_unembed cb etyp lam k  in
      let uu____61641 =
        let uu____61642 = type_of ea  in
        let uu____61643 =
          let uu____61644 = type_of eb  in as_iarg uu____61644  in
        make_arrow1 uu____61642 uu____61643  in
      mk_emb em un uu____61641 etyp
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____61662 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61662 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____61667 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61667 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____61672 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61672 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____61677 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61677 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____61682 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61682 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____61687 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61687 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____61692 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61692 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____61697 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61697 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____61702 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____61702 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____61711 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61712 =
          let uu____61713 =
            let uu____61718 =
              let uu____61719 = e_list e_string  in embed uu____61719 cb l
               in
            as_arg uu____61718  in
          [uu____61713]  in
        mkFV uu____61711 [] uu____61712
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____61741 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61742 =
          let uu____61743 =
            let uu____61748 =
              let uu____61749 = e_list e_string  in embed uu____61749 cb l
               in
            as_arg uu____61748  in
          [uu____61743]  in
        mkFV uu____61741 [] uu____61742
    | FStar_Syntax_Embeddings.UnfoldAttr l ->
        let uu____61771 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldattr
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____61772 =
          let uu____61773 =
            let uu____61778 =
              let uu____61779 = e_list e_string  in embed uu____61779 cb l
               in
            as_arg uu____61778  in
          [uu____61773]  in
        mkFV uu____61771 [] uu____61772
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____61813,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____61829,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____61845,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____61861,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____61877,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____61893,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____61909,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____61925,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____61941,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____61957,(l,uu____61959)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____61978 =
          let uu____61984 = e_list e_string  in unembed uu____61984 cb l  in
        FStar_Util.bind_opt uu____61978
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62004  -> FStar_Pervasives_Native.Some _62004)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____62006,(l,uu____62008)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____62027 =
          let uu____62033 = e_list e_string  in unembed uu____62033 cb l  in
        FStar_Util.bind_opt uu____62027
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62053  -> FStar_Pervasives_Native.Some _62053)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | FV (fv,uu____62055,(l,uu____62057)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldattr
        ->
        let uu____62076 =
          let uu____62082 = e_list e_string  in unembed uu____62082 cb l  in
        FStar_Util.bind_opt uu____62076
          (fun ss  ->
             FStar_All.pipe_left
               (fun _62102  -> FStar_Pervasives_Native.Some _62102)
               (FStar_Syntax_Embeddings.UnfoldAttr ss))
    | uu____62103 ->
        ((let uu____62105 =
            let uu____62111 =
              let uu____62113 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____62113
               in
            (FStar_Errors.Warning_NotEmbedded, uu____62111)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____62105);
         FStar_Pervasives_Native.None)
     in
  let uu____62117 =
    let uu____62118 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____62118 [] []  in
  let uu____62123 =
    FStar_Syntax_Embeddings.emb_typ_of FStar_Syntax_Embeddings.e_norm_step
     in
  mk_emb em un uu____62117 uu____62123 
let (bogus_cbs : nbe_cbs) =
  {
    iapp = (fun h  -> fun _args  -> h);
    translate = (fun uu____62132  -> failwith "bogus_cbs translate")
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
      let uu____62209 =
        let uu____62218 = e_list e  in unembed uu____62218 bogus_cbs  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____62209
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) FStar_Pervasives_Native.option)
  =
  fun uu____62240  ->
    match uu____62240 with
    | (a,uu____62248) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____62263)::[]) when
             let uu____62280 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____62280 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____62287 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cbs n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____62330 = let uu____62337 = as_arg c  in [uu____62337]  in
      int_to_t2 uu____62330
  
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
          let uu____62391 = f a  in FStar_Pervasives_Native.Some uu____62391
      | uu____62392 -> FStar_Pervasives_Native.None
  
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
          let uu____62446 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____62446
      | uu____62447 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____62491 = FStar_List.map as_a args  in
        lift_unary f uu____62491
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____62546 = FStar_List.map as_a args  in
        lift_binary f uu____62546
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____62576 = f x  in embed e_int bogus_cbs uu____62576)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  ->
           let uu____62603 = f x y  in embed e_int bogus_cbs uu____62603)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____62629 = f x  in embed e_bool bogus_cbs uu____62629)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____62667 = f x y  in embed e_bool bogus_cbs uu____62667)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____62705 = f x y  in embed e_string bogus_cbs uu____62705)
  
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
                let uu____62810 =
                  let uu____62819 = as_a a  in
                  let uu____62822 = as_b b  in (uu____62819, uu____62822)  in
                (match uu____62810 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____62837 =
                       let uu____62838 = f a1 b1  in embed_c uu____62838  in
                     FStar_Pervasives_Native.Some uu____62837
                 | uu____62839 -> FStar_Pervasives_Native.None)
            | uu____62848 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____62857 = e_list e_char  in
    let uu____62864 = FStar_String.list_of_string s  in
    embed uu____62857 bogus_cbs uu____62864
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____62903 =
        let uu____62904 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____62904  in
      embed e_int bogus_cbs uu____62903
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____62938 = arg_as_string a1  in
        (match uu____62938 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____62947 = arg_as_list e_string a2  in
             (match uu____62947 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____62965 = embed e_string bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____62965
              | uu____62967 -> FStar_Pervasives_Native.None)
         | uu____62973 -> FStar_Pervasives_Native.None)
    | uu____62977 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____62984 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cbs uu____62984
  
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
      | (_typ,uu____63046)::(a1,uu____63048)::(a2,uu____63050)::[] ->
          let uu____63067 = eq_t a1 a2  in
          (match uu____63067 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____63076 -> FStar_Pervasives_Native.None)
      | uu____63077 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq2 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____63092)::(_typ,uu____63094)::(a1,uu____63096)::(a2,uu____63098)::[]
        ->
        let uu____63119 = eq_t a1 a2  in
        (match uu____63119 with
         | FStar_Syntax_Util.Equal  ->
             let uu____63122 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____63122
         | FStar_Syntax_Util.NotEqual  ->
             let uu____63125 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____63125
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____63128 -> failwith "Unexpected number of arguments"
  
let (interp_prop_eq3 : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____63143)::(_v,uu____63145)::(t1,uu____63147)::(t2,uu____63149)::
        (a1,uu____63151)::(a2,uu____63153)::[] ->
        let uu____63182 =
          let uu____63183 = eq_t t1 t2  in
          let uu____63184 = eq_t a1 a2  in
          FStar_Syntax_Util.eq_inj uu____63183 uu____63184  in
        (match uu____63182 with
         | FStar_Syntax_Util.Equal  ->
             let uu____63187 = embed e_bool bogus_cbs true  in
             FStar_Pervasives_Native.Some uu____63187
         | FStar_Syntax_Util.NotEqual  ->
             let uu____63190 = embed e_bool bogus_cbs false  in
             FStar_Pervasives_Native.Some uu____63190
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____63193 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____63212 =
        let uu____63214 = FStar_Ident.string_of_lid lid  in
        FStar_String.op_Hat "No interpretation for " uu____63214  in
      failwith uu____63212
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____63230)::[] ->
        let uu____63239 = unembed e_range bogus_cbs a1  in
        (match uu____63239 with
         | FStar_Pervasives_Native.Some r ->
             let uu____63245 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____63245
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____63246 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63282 = arg_as_list e_char a1  in
        (match uu____63282 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____63298 = arg_as_string a2  in
             (match uu____63298 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____63311 =
                    let uu____63312 = e_list e_string  in
                    embed uu____63312 bogus_cbs r  in
                  FStar_Pervasives_Native.Some uu____63311
              | uu____63322 -> FStar_Pervasives_Native.None)
         | uu____63326 -> FStar_Pervasives_Native.None)
    | uu____63332 -> FStar_Pervasives_Native.None
  
let (string_index : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63365 =
          let uu____63375 = arg_as_string a1  in
          let uu____63379 = arg_as_int a2  in (uu____63375, uu____63379)  in
        (match uu____63365 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some i) ->
             (try
                (fun uu___1497_63403  ->
                   match () with
                   | () ->
                       let r = FStar_String.index s i  in
                       let uu____63408 = embed e_char bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63408) ()
              with | uu___1496_63411 -> FStar_Pervasives_Native.None)
         | uu____63414 -> FStar_Pervasives_Native.None)
    | uu____63424 -> FStar_Pervasives_Native.None
  
let (string_index_of : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____63457 =
          let uu____63468 = arg_as_string a1  in
          let uu____63472 = arg_as_char a2  in (uu____63468, uu____63472)  in
        (match uu____63457 with
         | (FStar_Pervasives_Native.Some s,FStar_Pervasives_Native.Some c) ->
             (try
                (fun uu___1515_63501  ->
                   match () with
                   | () ->
                       let r = FStar_String.index_of s c  in
                       let uu____63505 = embed e_int bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63505) ()
              with | uu___1514_63507 -> FStar_Pervasives_Native.None)
         | uu____63510 -> FStar_Pervasives_Native.None)
    | uu____63521 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____63563 =
          let uu____63577 = arg_as_string a1  in
          let uu____63581 = arg_as_int a2  in
          let uu____63584 = arg_as_int a3  in
          (uu____63577, uu____63581, uu____63584)  in
        (match uu____63563 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___1538_63617  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____63622 = embed e_string bogus_cbs r  in
                       FStar_Pervasives_Native.Some uu____63622) ()
              with | uu___1537_63625 -> FStar_Pervasives_Native.None)
         | uu____63628 -> FStar_Pervasives_Native.None)
    | uu____63642 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____63702 =
          let uu____63724 = arg_as_string fn  in
          let uu____63728 = arg_as_int from_line  in
          let uu____63731 = arg_as_int from_col  in
          let uu____63734 = arg_as_int to_line  in
          let uu____63737 = arg_as_int to_col  in
          (uu____63724, uu____63728, uu____63731, uu____63734, uu____63737)
           in
        (match uu____63702 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____63772 =
                 let uu____63773 = FStar_BigInt.to_int_fs from_l  in
                 let uu____63775 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____63773 uu____63775  in
               let uu____63777 =
                 let uu____63778 = FStar_BigInt.to_int_fs to_l  in
                 let uu____63780 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____63778 uu____63780  in
               FStar_Range.mk_range fn1 uu____63772 uu____63777  in
             let uu____63782 = embed e_range bogus_cbs r  in
             FStar_Pervasives_Native.Some uu____63782
         | uu____63783 -> FStar_Pervasives_Native.None)
    | uu____63805 -> FStar_Pervasives_Native.None
  
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
                let uu____63895 = FStar_List.splitAt n_tvars args  in
                match uu____63895 with
                | (_tvar_args,rest_args) ->
                    let uu____63944 = FStar_List.hd rest_args  in
                    (match uu____63944 with
                     | (x,uu____63956) ->
                         let uu____63957 = unembed ea cb x  in
                         FStar_Util.map_opt uu____63957
                           (fun x1  ->
                              let uu____63963 = f x1  in
                              embed eb cb uu____63963))
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
                  let uu____64072 = FStar_List.splitAt n_tvars args  in
                  match uu____64072 with
                  | (_tvar_args,rest_args) ->
                      let uu____64121 = FStar_List.hd rest_args  in
                      (match uu____64121 with
                       | (x,uu____64133) ->
                           let uu____64134 =
                             let uu____64139 = FStar_List.tl rest_args  in
                             FStar_List.hd uu____64139  in
                           (match uu____64134 with
                            | (y,uu____64157) ->
                                let uu____64158 = unembed ea cb x  in
                                FStar_Util.bind_opt uu____64158
                                  (fun x1  ->
                                     let uu____64164 = unembed eb cb y  in
                                     FStar_Util.bind_opt uu____64164
                                       (fun y1  ->
                                          let uu____64170 =
                                            let uu____64171 = f x1 y1  in
                                            embed ec cb uu____64171  in
                                          FStar_Pervasives_Native.Some
                                            uu____64170))))
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
                    let uu____64299 = FStar_List.splitAt n_tvars args  in
                    match uu____64299 with
                    | (_tvar_args,rest_args) ->
                        let uu____64348 = FStar_List.hd rest_args  in
                        (match uu____64348 with
                         | (x,uu____64360) ->
                             let uu____64361 =
                               let uu____64366 = FStar_List.tl rest_args  in
                               FStar_List.hd uu____64366  in
                             (match uu____64361 with
                              | (y,uu____64384) ->
                                  let uu____64385 =
                                    let uu____64390 =
                                      let uu____64397 =
                                        FStar_List.tl rest_args  in
                                      FStar_List.tl uu____64397  in
                                    FStar_List.hd uu____64390  in
                                  (match uu____64385 with
                                   | (z,uu____64419) ->
                                       let uu____64420 = unembed ea cb x  in
                                       FStar_Util.bind_opt uu____64420
                                         (fun x1  ->
                                            let uu____64426 = unembed eb cb y
                                               in
                                            FStar_Util.bind_opt uu____64426
                                              (fun y1  ->
                                                 let uu____64432 =
                                                   unembed ec cb z  in
                                                 FStar_Util.bind_opt
                                                   uu____64432
                                                   (fun z1  ->
                                                      let uu____64438 =
                                                        let uu____64439 =
                                                          f x1 y1 z1  in
                                                        embed ed cb
                                                          uu____64439
                                                         in
                                                      FStar_Pervasives_Native.Some
                                                        uu____64438))))))
                     in
                  f_wrapped
  