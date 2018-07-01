open Prims
type var = FStar_Syntax_Syntax.bv
type sort = Prims.int
type constant =
  | Unit 
  | Bool of Prims.bool 
  | Int of FStar_BigInt.t 
  | String of (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2
  
  | Char of FStar_Char.char 
  | Range of FStar_Range.range 
let (uu___is_Unit : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Unit  -> true | uu____36 -> false 
let (uu___is_Bool : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Bool _0 -> true | uu____43 -> false
  
let (__proj__Bool__item___0 : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Bool _0 -> _0 
let (uu___is_Int : constant -> Prims.bool) =
  fun projectee  -> match projectee with | Int _0 -> true | uu____57 -> false 
let (__proj__Int__item___0 : constant -> FStar_BigInt.t) =
  fun projectee  -> match projectee with | Int _0 -> _0 
let (uu___is_String : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | String _0 -> true | uu____75 -> false
  
let (__proj__String__item___0 :
  constant -> (Prims.string,FStar_Range.range) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | String _0 -> _0 
let (uu___is_Char : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Char _0 -> true | uu____102 -> false
  
let (__proj__Char__item___0 : constant -> FStar_Char.char) =
  fun projectee  -> match projectee with | Char _0 -> _0 
let (uu___is_Range : constant -> Prims.bool) =
  fun projectee  ->
    match projectee with | Range _0 -> true | uu____119 -> false
  
let (__proj__Range__item___0 : constant -> FStar_Range.range) =
  fun projectee  -> match projectee with | Range _0 -> _0 
type atom =
  | Var of var 
  | Match of
  (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
              FStar_Syntax_Syntax.branch Prims.list)
  FStar_Pervasives_Native.tuple3 
and t =
  | Lam of
  (t Prims.list -> t,(unit ->
                        (t,FStar_Syntax_Syntax.aqual)
                          FStar_Pervasives_Native.tuple2)
                       Prims.list,Prims.int)
  FStar_Pervasives_Native.tuple3 
  | Accu of
  (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
          Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Construct of
  (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
  FStar_Pervasives_Native.tuple3 
  | FV of
  (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
  FStar_Pervasives_Native.tuple3 
  | Constant of constant 
  | Type_t of FStar_Syntax_Syntax.universe 
  | Univ of FStar_Syntax_Syntax.universe 
  | Unknown 
  | Arrow of
  (t Prims.list -> comp,(unit ->
                           (t,FStar_Syntax_Syntax.aqual)
                             FStar_Pervasives_Native.tuple2)
                          Prims.list)
  FStar_Pervasives_Native.tuple2 
  | Refinement of
  (t -> t,unit ->
            (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
  FStar_Pervasives_Native.tuple2 
  | Quote of (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
  FStar_Pervasives_Native.tuple2 
  | Lazy of FStar_Syntax_Syntax.lazyinfo 
  | Rec of
  (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
  t Prims.list,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
                 Prims.list,Prims.int)
  FStar_Pervasives_Native.tuple5 
and comp =
  | Tot of (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | GTot of (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple2 
  | Comp of comp_typ 
and comp_typ =
  {
  comp_univs: FStar_Syntax_Syntax.universes ;
  effect_name: FStar_Ident.lident ;
  result_typ: t ;
  effect_args:
    (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list ;
  flags: FStar_Syntax_Syntax.cflags Prims.list }
let (uu___is_Var : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Var _0 -> true | uu____403 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____434 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____519 -> false
  
let (__proj__Lam__item___0 :
  t ->
    (t Prims.list -> t,(unit ->
                          (t,FStar_Syntax_Syntax.aqual)
                            FStar_Pervasives_Native.tuple2)
                         Prims.list,Prims.int)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____603 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____661 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____731 -> false 
let (__proj__FV__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | FV _0 -> _0 
let (uu___is_Constant : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Constant _0 -> true | uu____787 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____801 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____815 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____828 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____853 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    (t Prims.list -> comp,(unit ->
                             (t,FStar_Syntax_Syntax.aqual)
                               FStar_Pervasives_Native.tuple2)
                            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____935 -> false
  
let (__proj__Refinement__item___0 :
  t ->
    (t -> t,unit ->
              (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____995 -> false
  
let (__proj__Quote__item___0 :
  t ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1021 -> false
  
let (__proj__Lazy__item___0 : t -> FStar_Syntax_Syntax.lazyinfo) =
  fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1055 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
      t Prims.list,(t,FStar_Syntax_Syntax.aqual)
                     FStar_Pervasives_Native.tuple2 Prims.list,Prims.int)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1135 -> false
  
let (__proj__Tot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1173 -> false
  
let (__proj__GTot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1205 -> false
  
let (__proj__Comp__item___0 : comp -> comp_typ) =
  fun projectee  -> match projectee with | Comp _0 -> _0 
let (__proj__Mkcomp_typ__item__comp_univs :
  comp_typ -> FStar_Syntax_Syntax.universes) =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__comp_univs
  
let (__proj__Mkcomp_typ__item__effect_name : comp_typ -> FStar_Ident.lident)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__effect_name
  
let (__proj__Mkcomp_typ__item__result_typ : comp_typ -> t) =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__result_typ
  
let (__proj__Mkcomp_typ__item__effect_args :
  comp_typ ->
    (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__effect_args
  
let (__proj__Mkcomp_typ__item__flags :
  comp_typ -> FStar_Syntax_Syntax.cflags Prims.list) =
  fun projectee  ->
    match projectee with
    | { comp_univs = __fname__comp_univs; effect_name = __fname__effect_name;
        result_typ = __fname__result_typ; effect_args = __fname__effect_args;
        flags = __fname__flags;_} -> __fname__flags
  
type arg = (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
type args =
  (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2 Prims.list
type head = t
type annot = t FStar_Pervasives_Native.option
let (isAccu : t -> Prims.bool) =
  fun trm  -> match trm with | Accu uu____1336 -> true | uu____1347 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1353,uu____1354) -> false | uu____1367 -> true
  
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
  fun uu___222_1496  ->
    if uu___222_1496
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___223_1502  ->
    if uu___223_1502
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
      | (FStar_Syntax_Util.NotEqual ,uu____1514) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1515,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1516) -> FStar_Syntax_Util.Unknown
      | (uu____1517,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1533 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1549),String (s2,uu____1551)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1559,uu____1560) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1595,Lam uu____1596) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____1665 = eq_atom a1 a2  in
          eq_and uu____1665 (fun uu____1667  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____1706 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1706
          then
            let uu____1707 =
              let uu____1708 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1708  in
            eq_and uu____1707 (fun uu____1710  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____1750 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1750
          then
            let uu____1751 =
              let uu____1752 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1752  in
            eq_and uu____1751 (fun uu____1754  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____1760 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1760
      | (Univ u1,Univ u2) ->
          let uu____1763 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1763
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____1809 =
            let uu____1810 =
              let uu____1811 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1811  in
            let uu____1816 =
              let uu____1817 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1817  in
            eq_t uu____1810 uu____1816  in
          eq_and uu____1809
            (fun uu____1825  ->
               let uu____1826 =
                 let uu____1827 = mkAccuVar x  in r1 uu____1827  in
               let uu____1828 =
                 let uu____1829 = mkAccuVar x  in r2 uu____1829  in
               eq_t uu____1826 uu____1828)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____1830,uu____1831) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____1836,uu____1837) -> FStar_Syntax_Util.Unknown

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
          let uu____1918 = eq_arg x y  in
          eq_and uu____1918 (fun uu____1920  -> eq_args xs ys)
      | (uu____1921,uu____1922) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____1958) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____1960 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____1960
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam uu____1978 -> "Lam"
    | Accu (a,l) ->
        let uu____2013 =
          let uu____2014 = atom_to_string a  in
          let uu____2015 =
            let uu____2016 =
              let uu____2017 =
                let uu____2018 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2018  in
              Prims.strcat uu____2017 ")"  in
            Prims.strcat ") (" uu____2016  in
          Prims.strcat uu____2014 uu____2015  in
        Prims.strcat "Accu (" uu____2013
    | Construct (fv,us,l) ->
        let uu____2050 =
          let uu____2051 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2052 =
            let uu____2053 =
              let uu____2054 =
                let uu____2055 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2055  in
              let uu____2058 =
                let uu____2059 =
                  let uu____2060 =
                    let uu____2061 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2061  in
                  Prims.strcat uu____2060 "]"  in
                Prims.strcat "] [" uu____2059  in
              Prims.strcat uu____2054 uu____2058  in
            Prims.strcat ") [" uu____2053  in
          Prims.strcat uu____2051 uu____2052  in
        Prims.strcat "Construct (" uu____2050
    | FV (fv,us,l) ->
        let uu____2093 =
          let uu____2094 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2095 =
            let uu____2096 =
              let uu____2097 =
                let uu____2098 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2098  in
              let uu____2101 =
                let uu____2102 =
                  let uu____2103 =
                    let uu____2104 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2104  in
                  Prims.strcat uu____2103 "]"  in
                Prims.strcat "] [" uu____2102  in
              Prims.strcat uu____2097 uu____2101  in
            Prims.strcat ") [" uu____2096  in
          Prims.strcat uu____2094 uu____2095  in
        Prims.strcat "FV (" uu____2093
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2119 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____2119
    | Type_t u ->
        let uu____2121 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____2121
    | Arrow uu____2122 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____2165 = t ()  in FStar_Pervasives_Native.fst uu____2165
           in
        let uu____2170 =
          let uu____2171 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____2172 =
            let uu____2173 =
              let uu____2174 = t_to_string t1  in
              let uu____2175 =
                let uu____2176 =
                  let uu____2177 =
                    let uu____2178 =
                      let uu____2179 = mkAccuVar x1  in f uu____2179  in
                    t_to_string uu____2178  in
                  Prims.strcat uu____2177 "}"  in
                Prims.strcat "{" uu____2176  in
              Prims.strcat uu____2174 uu____2175  in
            Prims.strcat ":" uu____2173  in
          Prims.strcat uu____2171 uu____2172  in
        Prims.strcat "Refinement " uu____2170
    | Unknown  -> "Unknown"
    | Quote uu____2180 -> "Quote _"
    | Lazy uu____2185 -> "Lazy _"
    | Rec (uu____2186,uu____2187,l,uu____2189,uu____2190) ->
        let uu____2211 =
          let uu____2212 =
            let uu____2213 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2213  in
          Prims.strcat uu____2212 ")"  in
        Prims.strcat "Rec (" uu____2211

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____2218 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____2218
    | Match (t,uu____2220,uu____2221) ->
        let uu____2244 = t_to_string t  in Prims.strcat "Match " uu____2244

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2246 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2246 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2252 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2252 (FStar_String.concat " ")

type 'a embedding =
  {
  em: 'a -> t ;
  un: t -> 'a FStar_Pervasives_Native.option ;
  typ: t }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> 'a -> t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> t -> 'a FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__un
  
let __proj__Mkembedding__item__typ : 'a . 'a embedding -> t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__typ
  
let embed : 'a . 'a embedding -> 'a -> t = fun e  -> fun x  -> e.em x 
let unembed : 'a . 'a embedding -> t -> 'a FStar_Pervasives_Native.option =
  fun e  -> fun trm  -> e.un trm 
let type_of : 'a . 'a embedding -> t = fun e  -> e.typ 
let mk_emb :
  'Auu____2443 .
    ('Auu____2443 -> t) ->
      (t -> 'Auu____2443 FStar_Pervasives_Native.option) ->
        t -> 'Auu____2443 embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2494 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____2494 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2514 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkConstruct uu____2514 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____2550  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____2563  -> a)])
  
let (e_any : t embedding) =
  let em a = a  in
  let un t = FStar_Pervasives_Native.Some t  in
  let uu____2587 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____2587 
let (e_unit : unit embedding) =
  let em a = Constant Unit  in
  let un t = FStar_Pervasives_Native.Some ()  in
  let uu____2608 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  mk_emb em un uu____2608 
let (e_bool : Prims.bool embedding) =
  let em a = Constant (Bool a)  in
  let un t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____2634 -> FStar_Pervasives_Native.None  in
  let uu____2635 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  mk_emb em un uu____2635 
let (e_char : FStar_Char.char embedding) =
  let em c = Constant (Char c)  in
  let un c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____2669 -> FStar_Pervasives_Native.None  in
  let uu____2671 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  mk_emb em un uu____2671 
let (e_string : Prims.string embedding) =
  let em s = Constant (String (s, FStar_Range.dummyRange))  in
  let un s =
    match s with
    | Constant (String (s1,uu____2698)) -> FStar_Pervasives_Native.Some s1
    | uu____2699 -> FStar_Pervasives_Native.None  in
  let uu____2700 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  mk_emb em un uu____2700 
let (e_int : FStar_BigInt.t embedding) =
  let em c = Constant (Int c)  in
  let un c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____2726 -> FStar_Pervasives_Native.None  in
  let uu____2727 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  mk_emb em un uu____2727 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____2760 =
            let uu____2761 =
              let uu____2766 = type_of ea  in as_iarg uu____2766  in
            [uu____2761]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____2760
      | FStar_Pervasives_Native.Some x ->
          let uu____2776 =
            let uu____2777 =
              let uu____2782 = type_of ea  in as_iarg uu____2782  in
            let uu____2783 =
              let uu____2790 =
                let uu____2795 = embed ea x  in as_arg uu____2795  in
              [uu____2790]  in
            uu____2777 :: uu____2783  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____2776
       in
    let un trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,uu____2845::(a,uu____2847)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____2874 = unembed ea a  in
          FStar_Util.bind_opt uu____2874
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____2883 -> FStar_Pervasives_Native.None  in
    let uu____2886 =
      let uu____2887 =
        let uu____2888 = let uu____2893 = type_of ea  in as_arg uu____2893
           in
        [uu____2888]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____2887
       in
    mk_emb em un uu____2886
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em x =
        let uu____2952 =
          let uu____2953 = let uu____2958 = type_of ea  in as_iarg uu____2958
             in
          let uu____2959 =
            let uu____2966 =
              let uu____2971 = type_of eb  in as_iarg uu____2971  in
            let uu____2972 =
              let uu____2979 =
                let uu____2984 = embed ea (FStar_Pervasives_Native.fst x)  in
                as_arg uu____2984  in
              let uu____2985 =
                let uu____2992 =
                  let uu____2997 = embed eb (FStar_Pervasives_Native.snd x)
                     in
                  as_arg uu____2997  in
                [uu____2992]  in
              uu____2979 :: uu____2985  in
            uu____2966 :: uu____2972  in
          uu____2953 :: uu____2959  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____2952
         in
      let un trm =
        match trm with
        | Construct
            (fvar1,us,uu____3038::uu____3039::(a,uu____3041)::(b,uu____3043)::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____3082 = unembed ea a  in
            FStar_Util.bind_opt uu____3082
              (fun a1  ->
                 let uu____3092 = unembed eb b  in
                 FStar_Util.bind_opt uu____3092
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____3105 -> FStar_Pervasives_Native.None  in
      let uu____3110 =
        let uu____3111 =
          let uu____3112 = let uu____3117 = type_of ea  in as_arg uu____3117
             in
          let uu____3118 =
            let uu____3125 =
              let uu____3130 = type_of eb  in as_arg uu____3130  in
            [uu____3125]  in
          uu____3112 :: uu____3118  in
        lid_as_typ FStar_Parser_Const.lid_tuple2 [FStar_Syntax_Syntax.U_zero]
          uu____3111
         in
      mk_emb em un uu____3110
  
let (e_range : FStar_Range.range embedding) =
  let em r = Constant (Range r)  in
  let un t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____3168 -> FStar_Pervasives_Native.None  in
  let uu____3169 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  mk_emb em un uu____3169 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em l =
      let typ = let uu____3203 = type_of ea  in as_iarg uu____3203  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____3224 =
          let uu____3225 =
            let uu____3232 =
              let uu____3237 = embed ea hd1  in as_arg uu____3237  in
            let uu____3238 = let uu____3245 = as_arg tl1  in [uu____3245]  in
            uu____3232 :: uu____3238  in
          typ :: uu____3225  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____3224
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un trm =
      match trm with
      | Construct (fv,uu____3281,uu____3282) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____3302,(uu____3303,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____3304))::
           (hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                 )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3333 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3333
            (fun hd2  ->
               let uu____3341 = un tl1  in
               FStar_Util.bind_opt uu____3341
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____3357,(hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3382 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3382
            (fun hd2  ->
               let uu____3390 = un tl1  in
               FStar_Util.bind_opt uu____3390
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____3405 -> FStar_Pervasives_Native.None  in
    let uu____3408 =
      let uu____3409 =
        let uu____3410 = let uu____3415 = type_of ea  in as_arg uu____3415
           in
        [uu____3410]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____3409
       in
    mk_emb em un uu____3408
  
let e_arrow1 : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em f =
        Lam
          ((fun tas  ->
              let uu____3491 =
                let uu____3494 = FStar_List.hd tas  in unembed ea uu____3494
                 in
              match uu____3491 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____3496 = f a  in embed eb uu____3496
              | FStar_Pervasives_Native.None  ->
                  failwith "cannot unembed function argument"),
            [(fun uu____3506  ->
                let uu____3507 = type_of eb  in as_arg uu____3507)],
            (Prims.parse_int "1"))
         in
      let un lam =
        match lam with
        | Lam (ft,uu____3537,uu____3538) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____3574 =
                    let uu____3577 =
                      let uu____3578 =
                        let uu____3581 = embed ea x  in [uu____3581]  in
                      ft uu____3578  in
                    unembed eb uu____3577  in
                  match uu____3574 with
                  | FStar_Pervasives_Native.Some x1 -> x1
                  | FStar_Pervasives_Native.None  ->
                      failwith "cannot unembed function result"))
        | uu____3583 -> FStar_Pervasives_Native.None  in
      let uu____3587 =
        let uu____3588 = type_of ea  in
        let uu____3589 = let uu____3590 = type_of eb  in as_iarg uu____3590
           in
        make_arrow1 uu____3588 uu____3589  in
      mk_emb em un uu____3587
  
let (arg_as_int : arg -> FStar_BigInt.t FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_int)
  
let (arg_as_bool : arg -> Prims.bool FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_bool)
  
let (arg_as_char : arg -> FStar_Char.char FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_char)
  
let (arg_as_string : arg -> Prims.string FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a) (unembed e_string)
  
let arg_as_list :
  'a . 'a embedding -> arg -> 'a Prims.list FStar_Pervasives_Native.option =
  fun e  ->
    fun a  ->
      let uu____3658 = let uu____3667 = e_list e  in unembed uu____3667  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____3658
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____3688  ->
    match uu____3688 with
    | (a,uu____3696) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____3711)::[]) when
             let uu____3728 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____3728 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____3733 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____3775 = let uu____3782 = as_arg c  in [uu____3782]  in
      int_to_t2 uu____3775
  
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
          let uu____3835 = f a  in FStar_Pervasives_Native.Some uu____3835
      | uu____3836 -> FStar_Pervasives_Native.None
  
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
          let uu____3889 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____3889
      | uu____3890 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____3933 = FStar_List.map as_a args  in lift_unary f uu____3933
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____3987 = FStar_List.map as_a args  in
        lift_binary f uu____3987
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____4016 = f x  in embed e_int uu____4016)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  -> fun y  -> let uu____4042 = f x y  in embed e_int uu____4042)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____4061 = f x  in embed e_bool uu____4061)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  -> fun y  -> let uu____4087 = f x y  in embed e_bool uu____4087)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  -> let uu____4113 = f x y  in embed e_string uu____4113)
  
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
                let uu____4215 =
                  let uu____4224 = as_a a  in
                  let uu____4227 = as_b b  in (uu____4224, uu____4227)  in
                (match uu____4215 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____4242 =
                       let uu____4243 = f a1 b1  in embed_c uu____4243  in
                     FStar_Pervasives_Native.Some uu____4242
                 | uu____4244 -> FStar_Pervasives_Native.None)
            | uu____4253 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____4259 = e_list e_char  in
    let uu____4266 = FStar_String.list_of_string s  in
    embed uu____4259 uu____4266
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____4296 =
        let uu____4297 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____4297  in
      embed e_int uu____4296
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4329 = arg_as_string a1  in
        (match uu____4329 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4335 = arg_as_list e_string a2  in
             (match uu____4335 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____4348 = embed e_string r  in
                  FStar_Pervasives_Native.Some uu____4348
              | uu____4349 -> FStar_Pervasives_Native.None)
         | uu____4354 -> FStar_Pervasives_Native.None)
    | uu____4357 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____4363 = FStar_BigInt.string_of_big_int i  in
    embed e_string uu____4363
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool true  in
      let fal = embed e_bool false  in
      match args with
      | (_univ,uu____4389)::(_typ,uu____4391)::(a1,uu____4393)::(a2,uu____4395)::[]
          ->
          let uu____4416 = eq_t a1 a2  in
          (match uu____4416 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____4421 -> FStar_Pervasives_Native.None)
      | uu____4422 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____4435)::(_typ,uu____4437)::(a1,uu____4439)::(a2,uu____4441)::[]
        ->
        let uu____4462 = eq_t a1 a2  in
        (match uu____4462 with
         | FStar_Syntax_Util.Equal  ->
             let uu____4465 = embed e_bool true  in
             FStar_Pervasives_Native.Some uu____4465
         | FStar_Syntax_Util.NotEqual  ->
             let uu____4466 = embed e_bool false  in
             FStar_Pervasives_Native.Some uu____4466
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____4467 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____4484 =
        let uu____4485 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____4485  in
      failwith uu____4484
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____4498)::[] ->
        let uu____4507 = unembed e_range a1  in
        (match uu____4507 with
         | FStar_Pervasives_Native.Some r ->
             let uu____4513 = embed e_range r  in
             FStar_Pervasives_Native.Some uu____4513
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____4514 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4548 = arg_as_list e_char a1  in
        (match uu____4548 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4564 = arg_as_string a2  in
             (match uu____4564 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____4573 =
                    let uu____4574 = e_list e_string  in embed uu____4574 r
                     in
                  FStar_Pervasives_Native.Some uu____4573
              | uu____4581 -> FStar_Pervasives_Native.None)
         | uu____4584 -> FStar_Pervasives_Native.None)
    | uu____4590 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____4631 =
          let uu____4644 = arg_as_string a1  in
          let uu____4647 = arg_as_int a2  in
          let uu____4650 = arg_as_int a3  in
          (uu____4644, uu____4647, uu____4650)  in
        (match uu____4631 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                let r = FStar_String.substring s1 n11 n21  in
                let uu____4681 = embed e_string r  in
                FStar_Pervasives_Native.Some uu____4681
              with | uu____4687 -> FStar_Pervasives_Native.None)
         | uu____4688 -> FStar_Pervasives_Native.None)
    | uu____4701 -> FStar_Pervasives_Native.None
  