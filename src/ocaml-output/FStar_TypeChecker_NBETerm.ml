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
  (t Prims.list -> t,(t Prims.list ->
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
  (t Prims.list -> comp,(t Prims.list ->
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
                 Prims.list,Prims.int,Prims.bool Prims.list,t Prims.list ->
                                                              FStar_Syntax_Syntax.letbinding
                                                                -> t)
  FStar_Pervasives_Native.tuple7 
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
    match projectee with | Var _0 -> true | uu____423 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____454 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____541 -> false
  
let (__proj__Lam__item___0 :
  t ->
    (t Prims.list -> t,(t Prims.list ->
                          (t,FStar_Syntax_Syntax.aqual)
                            FStar_Pervasives_Native.tuple2)
                         Prims.list,Prims.int)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Lam _0 -> _0 
let (uu___is_Accu : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Accu _0 -> true | uu____631 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____689 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____759 -> false 
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
    match projectee with | Constant _0 -> true | uu____815 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____829 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____843 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____856 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____883 -> false
  
let (__proj__Arrow__item___0 :
  t ->
    (t Prims.list -> comp,(t Prims.list ->
                             (t,FStar_Syntax_Syntax.aqual)
                               FStar_Pervasives_Native.tuple2)
                            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Arrow _0 -> _0 
let (uu___is_Refinement : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Refinement _0 -> true | uu____971 -> false
  
let (__proj__Refinement__item___0 :
  t ->
    (t -> t,unit ->
              (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1031 -> false
  
let (__proj__Quote__item___0 :
  t ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1057 -> false
  
let (__proj__Lazy__item___0 : t -> FStar_Syntax_Syntax.lazyinfo) =
  fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1105 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
      t Prims.list,(t,FStar_Syntax_Syntax.aqual)
                     FStar_Pervasives_Native.tuple2 Prims.list,Prims.int,
      Prims.bool Prims.list,t Prims.list ->
                              FStar_Syntax_Syntax.letbinding -> t)
      FStar_Pervasives_Native.tuple7)
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1227 -> false
  
let (__proj__Tot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1265 -> false
  
let (__proj__GTot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1297 -> false
  
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
  fun trm  -> match trm with | Accu uu____1428 -> true | uu____1439 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1445,uu____1446) -> false | uu____1459 -> true
  
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
  fun uu___226_1588  ->
    if uu___226_1588
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___227_1594  ->
    if uu___227_1594
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
      | (FStar_Syntax_Util.NotEqual ,uu____1606) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1607,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1608) -> FStar_Syntax_Util.Unknown
      | (uu____1609,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1625 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1641),String (s2,uu____1643)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1651,uu____1652) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1687,Lam uu____1688) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____1761 = eq_atom a1 a2  in
          eq_and uu____1761 (fun uu____1763  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____1802 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1802
          then
            let uu____1803 =
              let uu____1804 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1804  in
            eq_and uu____1803 (fun uu____1806  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____1846 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1846
          then
            let uu____1847 =
              let uu____1848 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1848  in
            eq_and uu____1847 (fun uu____1850  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____1856 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1856
      | (Univ u1,Univ u2) ->
          let uu____1859 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1859
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____1905 =
            let uu____1906 =
              let uu____1907 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1907  in
            let uu____1912 =
              let uu____1913 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1913  in
            eq_t uu____1906 uu____1912  in
          eq_and uu____1905
            (fun uu____1921  ->
               let uu____1922 =
                 let uu____1923 = mkAccuVar x  in r1 uu____1923  in
               let uu____1924 =
                 let uu____1925 = mkAccuVar x  in r2 uu____1925  in
               eq_t uu____1922 uu____1924)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____1926,uu____1927) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____1932,uu____1933) -> FStar_Syntax_Util.Unknown

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
          let uu____2014 = eq_arg x y  in
          eq_and uu____2014 (fun uu____2016  -> eq_args xs ys)
      | (uu____2017,uu____2018) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2054) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2056 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2056
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity) ->
        let uu____2109 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2119 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____2109 uu____2119
    | Accu (a,l) ->
        let uu____2134 =
          let uu____2135 = atom_to_string a  in
          let uu____2136 =
            let uu____2137 =
              let uu____2138 =
                let uu____2139 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2139  in
              Prims.strcat uu____2138 ")"  in
            Prims.strcat ") (" uu____2137  in
          Prims.strcat uu____2135 uu____2136  in
        Prims.strcat "Accu (" uu____2134
    | Construct (fv,us,l) ->
        let uu____2171 =
          let uu____2172 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2173 =
            let uu____2174 =
              let uu____2175 =
                let uu____2176 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2176  in
              let uu____2179 =
                let uu____2180 =
                  let uu____2181 =
                    let uu____2182 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2182  in
                  Prims.strcat uu____2181 "]"  in
                Prims.strcat "] [" uu____2180  in
              Prims.strcat uu____2175 uu____2179  in
            Prims.strcat ") [" uu____2174  in
          Prims.strcat uu____2172 uu____2173  in
        Prims.strcat "Construct (" uu____2171
    | FV (fv,us,l) ->
        let uu____2214 =
          let uu____2215 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2216 =
            let uu____2217 =
              let uu____2218 =
                let uu____2219 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2219  in
              let uu____2222 =
                let uu____2223 =
                  let uu____2224 =
                    let uu____2225 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2225  in
                  Prims.strcat uu____2224 "]"  in
                Prims.strcat "] [" uu____2223  in
              Prims.strcat uu____2218 uu____2222  in
            Prims.strcat ") [" uu____2217  in
          Prims.strcat uu____2215 uu____2216  in
        Prims.strcat "FV (" uu____2214
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2240 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____2240
    | Type_t u ->
        let uu____2242 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____2242
    | Arrow uu____2243 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____2288 = t ()  in FStar_Pervasives_Native.fst uu____2288
           in
        let uu____2293 =
          let uu____2294 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____2295 =
            let uu____2296 =
              let uu____2297 = t_to_string t1  in
              let uu____2298 =
                let uu____2299 =
                  let uu____2300 =
                    let uu____2301 =
                      let uu____2302 = mkAccuVar x1  in f uu____2302  in
                    t_to_string uu____2301  in
                  Prims.strcat uu____2300 "}"  in
                Prims.strcat "{" uu____2299  in
              Prims.strcat uu____2297 uu____2298  in
            Prims.strcat ":" uu____2296  in
          Prims.strcat uu____2294 uu____2295  in
        Prims.strcat "Refinement " uu____2293
    | Unknown  -> "Unknown"
    | Quote uu____2303 -> "Quote _"
    | Lazy uu____2308 -> "Lazy _"
    | Rec
        (uu____2309,uu____2310,l,uu____2312,uu____2313,uu____2314,uu____2315)
        ->
        let uu____2356 =
          let uu____2357 =
            let uu____2358 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2358  in
          Prims.strcat uu____2357 ")"  in
        Prims.strcat "Rec (" uu____2356

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____2363 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____2363
    | Match (t,uu____2365,uu____2366) ->
        let uu____2389 = t_to_string t  in Prims.strcat "Match " uu____2389

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2391 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2391 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2397 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2397 (FStar_String.concat " ")

type iapp_cb = t -> args -> t
type 'a embedding =
  {
  em: iapp_cb -> 'a -> t ;
  un: iapp_cb -> t -> 'a FStar_Pervasives_Native.option ;
  typ: t }
let __proj__Mkembedding__item__em : 'a . 'a embedding -> iapp_cb -> 'a -> t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__em
  
let __proj__Mkembedding__item__un :
  'a . 'a embedding -> iapp_cb -> t -> 'a FStar_Pervasives_Native.option =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__un
  
let __proj__Mkembedding__item__typ : 'a . 'a embedding -> t =
  fun projectee  ->
    match projectee with
    | { em = __fname__em; un = __fname__un; typ = __fname__typ;_} ->
        __fname__typ
  
let embed : 'a . 'a embedding -> iapp_cb -> 'a -> t =
  fun e  -> fun cb  -> fun x  -> e.em cb x 
let unembed :
  'a . 'a embedding -> iapp_cb -> t -> 'a FStar_Pervasives_Native.option =
  fun e  -> fun cb  -> fun trm  -> e.un cb trm 
let type_of : 'a . 'a embedding -> t = fun e  -> e.typ 
let mk_emb :
  'a .
    (iapp_cb -> 'a -> t) ->
      (iapp_cb -> t -> 'a FStar_Pervasives_Native.option) ->
        t -> 'a embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2789 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____2789 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2809 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkConstruct uu____2809 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____2847  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____2862  -> a)])
  
let (e_any : t embedding) =
  let em _cb a = a  in
  let un _cb t = FStar_Pervasives_Native.Some t  in
  let uu____2922 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____2922 
let (e_unit : unit embedding) =
  let em _cb a = Constant Unit  in
  let un _cb t = FStar_Pervasives_Native.Some ()  in
  let uu____2975 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  mk_emb em un uu____2975 
let (e_bool : Prims.bool embedding) =
  let em _cb a = Constant (Bool a)  in
  let un _cb t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____3031 -> FStar_Pervasives_Native.None  in
  let uu____3032 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  mk_emb em un uu____3032 
let (e_char : FStar_Char.char embedding) =
  let em _cb c = Constant (Char c)  in
  let un _cb c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____3096 -> FStar_Pervasives_Native.None  in
  let uu____3098 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  mk_emb em un uu____3098 
let (e_string : Prims.string embedding) =
  let em _cb s = Constant (String (s, FStar_Range.dummyRange))  in
  let un _cb s =
    match s with
    | Constant (String (s1,uu____3155)) -> FStar_Pervasives_Native.Some s1
    | uu____3156 -> FStar_Pervasives_Native.None  in
  let uu____3157 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  mk_emb em un uu____3157 
let (e_int : FStar_BigInt.t embedding) =
  let em _cb c = Constant (Int c)  in
  let un _cb c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____3213 -> FStar_Pervasives_Native.None  in
  let uu____3214 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  mk_emb em un uu____3214 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em cb o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____3262 =
            let uu____3263 =
              let uu____3268 = type_of ea  in as_iarg uu____3268  in
            [uu____3263]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____3262
      | FStar_Pervasives_Native.Some x ->
          let uu____3278 =
            let uu____3279 =
              let uu____3284 = embed ea cb x  in as_arg uu____3284  in
            let uu____3289 =
              let uu____3296 =
                let uu____3301 = type_of ea  in as_iarg uu____3301  in
              [uu____3296]  in
            uu____3279 :: uu____3289  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____3278
       in
    let un cb trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,(a,uu____3367)::uu____3368::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____3395 = unembed ea cb a  in
          FStar_Util.bind_opt uu____3395
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____3408 -> FStar_Pervasives_Native.None  in
    let uu____3411 =
      let uu____3412 =
        let uu____3413 = let uu____3418 = type_of ea  in as_arg uu____3418
           in
        [uu____3413]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____3412
       in
    mk_emb em un uu____3411
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em cb x =
        let uu____3492 =
          let uu____3493 =
            let uu____3498 = embed eb cb (FStar_Pervasives_Native.snd x)  in
            as_arg uu____3498  in
          let uu____3503 =
            let uu____3510 =
              let uu____3515 = embed ea cb (FStar_Pervasives_Native.fst x)
                 in
              as_arg uu____3515  in
            let uu____3520 =
              let uu____3527 =
                let uu____3532 = type_of eb  in as_iarg uu____3532  in
              let uu____3533 =
                let uu____3540 =
                  let uu____3545 = type_of ea  in as_iarg uu____3545  in
                [uu____3540]  in
              uu____3527 :: uu____3533  in
            uu____3510 :: uu____3520  in
          uu____3493 :: uu____3503  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____3492
         in
      let un cb trm =
        match trm with
        | Construct
            (fvar1,us,(b,uu____3602)::(a,uu____3604)::uu____3605::uu____3606::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____3645 = unembed ea cb a  in
            FStar_Util.bind_opt uu____3645
              (fun a1  ->
                 let uu____3659 = unembed eb cb b  in
                 FStar_Util.bind_opt uu____3659
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____3676 -> FStar_Pervasives_Native.None  in
      let uu____3681 =
        let uu____3682 =
          let uu____3683 = let uu____3688 = type_of eb  in as_arg uu____3688
             in
          let uu____3689 =
            let uu____3696 =
              let uu____3701 = type_of ea  in as_arg uu____3701  in
            [uu____3696]  in
          uu____3683 :: uu____3689  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____3682
         in
      mk_emb em un uu____3681
  
let e_either :
  'a 'b . 'a embedding -> 'b embedding -> ('a,'b) FStar_Util.either embedding
  =
  fun ea  ->
    fun eb  ->
      let em cb s =
        match s with
        | FStar_Util.Inl a ->
            let uu____3782 =
              let uu____3783 =
                let uu____3788 = embed ea cb a  in as_arg uu____3788  in
              let uu____3793 =
                let uu____3800 =
                  let uu____3805 = type_of eb  in as_iarg uu____3805  in
                let uu____3806 =
                  let uu____3813 =
                    let uu____3818 = type_of ea  in as_iarg uu____3818  in
                  [uu____3813]  in
                uu____3800 :: uu____3806  in
              uu____3783 :: uu____3793  in
            lid_as_constr FStar_Parser_Const.inl_lid
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
              uu____3782
        | FStar_Util.Inr b ->
            let uu____3836 =
              let uu____3837 =
                let uu____3842 = embed eb cb b  in as_arg uu____3842  in
              let uu____3847 =
                let uu____3854 =
                  let uu____3859 = type_of eb  in as_iarg uu____3859  in
                let uu____3860 =
                  let uu____3867 =
                    let uu____3872 = type_of ea  in as_iarg uu____3872  in
                  [uu____3867]  in
                uu____3854 :: uu____3860  in
              uu____3837 :: uu____3847  in
            lid_as_constr FStar_Parser_Const.inr_lid
              [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero]
              uu____3836
         in
      let un cb trm =
        match trm with
        | Construct (fvar1,us,(a,uu____3925)::uu____3926::uu____3927::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.inl_lid ->
            let uu____3962 = unembed ea cb a  in
            FStar_Util.bind_opt uu____3962
              (fun a1  -> FStar_Pervasives_Native.Some (FStar_Util.Inl a1))
        | Construct (fvar1,us,(b,uu____3982)::uu____3983::uu____3984::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.inr_lid ->
            let uu____4019 = unembed eb cb b  in
            FStar_Util.bind_opt uu____4019
              (fun b1  -> FStar_Pervasives_Native.Some (FStar_Util.Inr b1))
        | uu____4036 -> FStar_Pervasives_Native.None  in
      let uu____4041 =
        let uu____4042 =
          let uu____4043 = let uu____4048 = type_of eb  in as_arg uu____4048
             in
          let uu____4049 =
            let uu____4056 =
              let uu____4061 = type_of ea  in as_arg uu____4061  in
            [uu____4056]  in
          uu____4043 :: uu____4049  in
        lid_as_typ FStar_Parser_Const.either_lid
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____4042
         in
      mk_emb em un uu____4041
  
let (e_range : FStar_Range.range embedding) =
  let em cb r = Constant (Range r)  in
  let un cb t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____4129 -> FStar_Pervasives_Native.None  in
  let uu____4130 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  mk_emb em un uu____4130 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em cb l =
      let typ = let uu____4179 = type_of ea  in as_iarg uu____4179  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____4200 =
          let uu____4201 = as_arg tl1  in
          let uu____4206 =
            let uu____4213 =
              let uu____4218 = embed ea cb hd1  in as_arg uu____4218  in
            [uu____4213; typ]  in
          uu____4201 :: uu____4206  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____4200
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un cb trm =
      match trm with
      | Construct (fv,uu____4269,uu____4270) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____4290,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                               )::(uu____4293,FStar_Pervasives_Native.Some
                                                                   (FStar_Syntax_Syntax.Implicit
                                                                   uu____4294))::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____4321 = unembed ea cb hd1  in
          FStar_Util.bind_opt uu____4321
            (fun hd2  ->
               let uu____4333 = un cb tl1  in
               FStar_Util.bind_opt uu____4333
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____4355,(tl1,FStar_Pervasives_Native.None )::(hd1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____4380 = unembed ea cb hd1  in
          FStar_Util.bind_opt uu____4380
            (fun hd2  ->
               let uu____4392 = un cb tl1  in
               FStar_Util.bind_opt uu____4392
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____4413 -> FStar_Pervasives_Native.None  in
    let uu____4416 =
      let uu____4417 =
        let uu____4418 = let uu____4423 = type_of ea  in as_arg uu____4423
           in
        [uu____4418]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____4417
       in
    mk_emb em un uu____4416
  
let (e_string_list : Prims.string Prims.list embedding) = e_list e_string 
let e_arrow1 : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em cb f =
        Lam
          ((fun tas  ->
              let uu____4520 =
                let uu____4523 = FStar_List.hd tas  in
                unembed ea cb uu____4523  in
              match uu____4520 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____4529 = f a  in embed eb cb uu____4529
              | FStar_Pervasives_Native.None  ->
                  failwith "cannot unembed function argument"),
            [(fun uu____4545  ->
                let uu____4548 = type_of eb  in as_arg uu____4548)],
            (Prims.parse_int "1"))
         in
      let un cb lam =
        match lam with
        | Lam (ft,uu____4595,uu____4596) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____4636 =
                    let uu____4639 =
                      let uu____4640 =
                        let uu____4643 = embed ea cb x  in [uu____4643]  in
                      ft uu____4640  in
                    unembed eb cb uu____4639  in
                  match uu____4636 with
                  | FStar_Pervasives_Native.Some x1 -> x1
                  | FStar_Pervasives_Native.None  ->
                      failwith "cannot unembed function result"))
        | uu____4653 -> FStar_Pervasives_Native.None  in
      let uu____4657 =
        let uu____4658 = type_of ea  in
        let uu____4659 = let uu____4660 = type_of eb  in as_iarg uu____4660
           in
        make_arrow1 uu____4658 uu____4659  in
      mk_emb em un uu____4657
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em cb n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____4687 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4687 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____4692 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4692 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____4697 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4697 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____4702 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4702 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____4707 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4707 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____4712 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4712 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____4717 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4717 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____4722 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4722 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____4727 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____4727 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____4735 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____4736 =
          let uu____4737 =
            let uu____4742 =
              let uu____4743 = e_list e_string  in embed uu____4743 cb l  in
            as_arg uu____4742  in
          [uu____4737]  in
        mkFV uu____4735 [] uu____4736
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____4765 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____4766 =
          let uu____4767 =
            let uu____4772 =
              let uu____4773 = e_list e_string  in embed uu____4773 cb l  in
            as_arg uu____4772  in
          [uu____4767]  in
        mkFV uu____4765 [] uu____4766
    | FStar_Syntax_Embeddings.UnfoldAttr a -> failwith "NBE UnfoldAttr..."
     in
  let un cb t0 =
    match t0 with
    | FV (fv,uu____4819,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____4835,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____4851,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____4867,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____4883,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____4899,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____4915,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____4931,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____4947,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____4963,(l,uu____4965)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____4984 =
          let uu____4989 = e_list e_string  in unembed uu____4989 cb l  in
        FStar_Util.bind_opt uu____4984
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____5009,(l,uu____5011)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____5030 =
          let uu____5035 = e_list e_string  in unembed uu____5035 cb l  in
        FStar_Util.bind_opt uu____5030
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | uu____5054 ->
        ((let uu____5056 =
            let uu____5061 =
              let uu____5062 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____5062
               in
            (FStar_Errors.Warning_NotEmbedded, uu____5061)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____5056);
         FStar_Pervasives_Native.None)
     in
  let uu____5063 =
    let uu____5064 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____5064 [] []  in
  mk_emb em un uu____5063 
let bogus_cb :
  'Auu____5077 'Auu____5078 . 'Auu____5077 -> 'Auu____5078 -> 'Auu____5077 =
  fun h  -> fun _args  -> h 
let (arg_as_int : arg -> FStar_BigInt.t FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_int bogus_cb)
  
let (arg_as_bool : arg -> Prims.bool FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_bool bogus_cb)
  
let (arg_as_char : arg -> FStar_Char.char FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_char bogus_cb)
  
let (arg_as_string : arg -> Prims.string FStar_Pervasives_Native.option) =
  fun a  ->
    FStar_All.pipe_right (FStar_Pervasives_Native.fst a)
      (unembed e_string bogus_cb)
  
let arg_as_list :
  'a . 'a embedding -> arg -> 'a Prims.list FStar_Pervasives_Native.option =
  fun e  ->
    fun a  ->
      let uu____5153 =
        let uu____5162 = e_list e  in unembed uu____5162 bogus_cb  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____5153
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____5183  ->
    match uu____5183 with
    | (a,uu____5191) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____5206)::[]) when
             let uu____5223 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____5223 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____5228 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int bogus_cb n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____5270 = let uu____5277 = as_arg c  in [uu____5277]  in
      int_to_t2 uu____5270
  
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
          let uu____5330 = f a  in FStar_Pervasives_Native.Some uu____5330
      | uu____5331 -> FStar_Pervasives_Native.None
  
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
          let uu____5384 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____5384
      | uu____5385 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____5428 = FStar_List.map as_a args  in lift_unary f uu____5428
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____5482 = FStar_List.map as_a args  in
        lift_binary f uu____5482
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____5511 = f x  in embed e_int bogus_cb uu____5511)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  ->
         fun y  -> let uu____5537 = f x y  in embed e_int bogus_cb uu____5537)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____5556 = f x  in embed e_bool bogus_cb uu____5556)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  ->
         fun y  ->
           let uu____5582 = f x y  in embed e_bool bogus_cb uu____5582)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  ->
           let uu____5608 = f x y  in embed e_string bogus_cb uu____5608)
  
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
                let uu____5710 =
                  let uu____5719 = as_a a  in
                  let uu____5722 = as_b b  in (uu____5719, uu____5722)  in
                (match uu____5710 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____5737 =
                       let uu____5738 = f a1 b1  in embed_c uu____5738  in
                     FStar_Pervasives_Native.Some uu____5737
                 | uu____5739 -> FStar_Pervasives_Native.None)
            | uu____5748 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____5754 = e_list e_char  in
    let uu____5761 = FStar_String.list_of_string s  in
    embed uu____5754 bogus_cb uu____5761
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____5791 =
        let uu____5792 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____5792  in
      embed e_int bogus_cb uu____5791
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____5824 = arg_as_string a1  in
        (match uu____5824 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5830 = arg_as_list e_string a2  in
             (match uu____5830 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____5843 = embed e_string bogus_cb r  in
                  FStar_Pervasives_Native.Some uu____5843
              | uu____5844 -> FStar_Pervasives_Native.None)
         | uu____5849 -> FStar_Pervasives_Native.None)
    | uu____5852 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____5858 = FStar_BigInt.string_of_big_int i  in
    embed e_string bogus_cb uu____5858
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string bogus_cb (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool bogus_cb true  in
      let fal = embed e_bool bogus_cb false  in
      match args with
      | (_univ,uu____5884)::(_typ,uu____5886)::(a1,uu____5888)::(a2,uu____5890)::[]
          ->
          let uu____5911 = eq_t a1 a2  in
          (match uu____5911 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____5916 -> FStar_Pervasives_Native.None)
      | uu____5917 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____5930)::(_typ,uu____5932)::(a1,uu____5934)::(a2,uu____5936)::[]
        ->
        let uu____5957 = eq_t a1 a2  in
        (match uu____5957 with
         | FStar_Syntax_Util.Equal  ->
             let uu____5960 = embed e_bool bogus_cb true  in
             FStar_Pervasives_Native.Some uu____5960
         | FStar_Syntax_Util.NotEqual  ->
             let uu____5961 = embed e_bool bogus_cb false  in
             FStar_Pervasives_Native.Some uu____5961
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____5962 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____5979 =
        let uu____5980 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____5980  in
      failwith uu____5979
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____5993)::[] ->
        let uu____6002 = unembed e_range bogus_cb a1  in
        (match uu____6002 with
         | FStar_Pervasives_Native.Some r ->
             let uu____6008 = embed e_range bogus_cb r  in
             FStar_Pervasives_Native.Some uu____6008
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____6009 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____6043 = arg_as_list e_char a1  in
        (match uu____6043 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____6059 = arg_as_string a2  in
             (match uu____6059 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____6068 =
                    let uu____6069 = e_list e_string  in
                    embed uu____6069 bogus_cb r  in
                  FStar_Pervasives_Native.Some uu____6068
              | uu____6076 -> FStar_Pervasives_Native.None)
         | uu____6079 -> FStar_Pervasives_Native.None)
    | uu____6085 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____6126 =
          let uu____6139 = arg_as_string a1  in
          let uu____6142 = arg_as_int a2  in
          let uu____6145 = arg_as_int a3  in
          (uu____6139, uu____6142, uu____6145)  in
        (match uu____6126 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___229_6172  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____6176 = embed e_string bogus_cb r  in
                       FStar_Pervasives_Native.Some uu____6176) ()
              with | uu___228_6178 -> FStar_Pervasives_Native.None)
         | uu____6181 -> FStar_Pervasives_Native.None)
    | uu____6194 -> FStar_Pervasives_Native.None
  
let (mk_range : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | fn::from_line::from_col::to_line::to_col::[] ->
        let uu____6253 =
          let uu____6274 = arg_as_string fn  in
          let uu____6277 = arg_as_int from_line  in
          let uu____6280 = arg_as_int from_col  in
          let uu____6283 = arg_as_int to_line  in
          let uu____6286 = arg_as_int to_col  in
          (uu____6274, uu____6277, uu____6280, uu____6283, uu____6286)  in
        (match uu____6253 with
         | (FStar_Pervasives_Native.Some fn1,FStar_Pervasives_Native.Some
            from_l,FStar_Pervasives_Native.Some
            from_c,FStar_Pervasives_Native.Some
            to_l,FStar_Pervasives_Native.Some to_c) ->
             let r =
               let uu____6317 =
                 let uu____6318 = FStar_BigInt.to_int_fs from_l  in
                 let uu____6319 = FStar_BigInt.to_int_fs from_c  in
                 FStar_Range.mk_pos uu____6318 uu____6319  in
               let uu____6320 =
                 let uu____6321 = FStar_BigInt.to_int_fs to_l  in
                 let uu____6322 = FStar_BigInt.to_int_fs to_c  in
                 FStar_Range.mk_pos uu____6321 uu____6322  in
               FStar_Range.mk_range fn1 uu____6317 uu____6320  in
             let uu____6323 = embed e_range bogus_cb r  in
             FStar_Pervasives_Native.Some uu____6323
         | uu____6324 -> FStar_Pervasives_Native.None)
    | uu____6345 -> FStar_Pervasives_Native.None
  