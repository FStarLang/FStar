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
    match projectee with | Var _0 -> true | uu____405 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____436 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____523 -> false
  
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
    match projectee with | Accu _0 -> true | uu____613 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____671 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____741 -> false 
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
    match projectee with | Constant _0 -> true | uu____797 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____811 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____825 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____838 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____863 -> false
  
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
    match projectee with | Refinement _0 -> true | uu____945 -> false
  
let (__proj__Refinement__item___0 :
  t ->
    (t -> t,unit ->
              (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1005 -> false
  
let (__proj__Quote__item___0 :
  t ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1031 -> false
  
let (__proj__Lazy__item___0 : t -> FStar_Syntax_Syntax.lazyinfo) =
  fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1065 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
      t Prims.list,(t,FStar_Syntax_Syntax.aqual)
                     FStar_Pervasives_Native.tuple2 Prims.list,Prims.int)
      FStar_Pervasives_Native.tuple5)
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1145 -> false
  
let (__proj__Tot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1183 -> false
  
let (__proj__GTot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1215 -> false
  
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
  fun trm  -> match trm with | Accu uu____1346 -> true | uu____1357 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1363,uu____1364) -> false | uu____1377 -> true
  
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
  fun uu___222_1506  ->
    if uu___222_1506
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___223_1512  ->
    if uu___223_1512
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
      | (FStar_Syntax_Util.NotEqual ,uu____1524) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1525,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1526) -> FStar_Syntax_Util.Unknown
      | (uu____1527,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1543 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1559),String (s2,uu____1561)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1569,uu____1570) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1605,Lam uu____1606) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____1679 = eq_atom a1 a2  in
          eq_and uu____1679 (fun uu____1681  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____1720 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1720
          then
            let uu____1721 =
              let uu____1722 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1722  in
            eq_and uu____1721 (fun uu____1724  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____1764 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1764
          then
            let uu____1765 =
              let uu____1766 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1766  in
            eq_and uu____1765 (fun uu____1768  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____1774 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1774
      | (Univ u1,Univ u2) ->
          let uu____1777 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1777
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____1823 =
            let uu____1824 =
              let uu____1825 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1825  in
            let uu____1830 =
              let uu____1831 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1831  in
            eq_t uu____1824 uu____1830  in
          eq_and uu____1823
            (fun uu____1839  ->
               let uu____1840 =
                 let uu____1841 = mkAccuVar x  in r1 uu____1841  in
               let uu____1842 =
                 let uu____1843 = mkAccuVar x  in r2 uu____1843  in
               eq_t uu____1840 uu____1842)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____1844,uu____1845) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____1850,uu____1851) -> FStar_Syntax_Util.Unknown

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
          let uu____1932 = eq_arg x y  in
          eq_and uu____1932 (fun uu____1934  -> eq_args xs ys)
      | (uu____1935,uu____1936) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____1972) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____1974 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____1974
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam uu____1992 -> "Lam"
    | Accu (a,l) ->
        let uu____2029 =
          let uu____2030 = atom_to_string a  in
          let uu____2031 =
            let uu____2032 =
              let uu____2033 =
                let uu____2034 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2034  in
              Prims.strcat uu____2033 ")"  in
            Prims.strcat ") (" uu____2032  in
          Prims.strcat uu____2030 uu____2031  in
        Prims.strcat "Accu (" uu____2029
    | Construct (fv,us,l) ->
        let uu____2066 =
          let uu____2067 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2068 =
            let uu____2069 =
              let uu____2070 =
                let uu____2071 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2071  in
              let uu____2074 =
                let uu____2075 =
                  let uu____2076 =
                    let uu____2077 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2077  in
                  Prims.strcat uu____2076 "]"  in
                Prims.strcat "] [" uu____2075  in
              Prims.strcat uu____2070 uu____2074  in
            Prims.strcat ") [" uu____2069  in
          Prims.strcat uu____2067 uu____2068  in
        Prims.strcat "Construct (" uu____2066
    | FV (fv,us,l) ->
        let uu____2109 =
          let uu____2110 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2111 =
            let uu____2112 =
              let uu____2113 =
                let uu____2114 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2114  in
              let uu____2117 =
                let uu____2118 =
                  let uu____2119 =
                    let uu____2120 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2120  in
                  Prims.strcat uu____2119 "]"  in
                Prims.strcat "] [" uu____2118  in
              Prims.strcat uu____2113 uu____2117  in
            Prims.strcat ") [" uu____2112  in
          Prims.strcat uu____2110 uu____2111  in
        Prims.strcat "FV (" uu____2109
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2135 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____2135
    | Type_t u ->
        let uu____2137 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____2137
    | Arrow uu____2138 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____2181 = t ()  in FStar_Pervasives_Native.fst uu____2181
           in
        let uu____2186 =
          let uu____2187 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____2188 =
            let uu____2189 =
              let uu____2190 = t_to_string t1  in
              let uu____2191 =
                let uu____2192 =
                  let uu____2193 =
                    let uu____2194 =
                      let uu____2195 = mkAccuVar x1  in f uu____2195  in
                    t_to_string uu____2194  in
                  Prims.strcat uu____2193 "}"  in
                Prims.strcat "{" uu____2192  in
              Prims.strcat uu____2190 uu____2191  in
            Prims.strcat ":" uu____2189  in
          Prims.strcat uu____2187 uu____2188  in
        Prims.strcat "Refinement " uu____2186
    | Unknown  -> "Unknown"
    | Quote uu____2196 -> "Quote _"
    | Lazy uu____2201 -> "Lazy _"
    | Rec (uu____2202,uu____2203,l,uu____2205,uu____2206) ->
        let uu____2227 =
          let uu____2228 =
            let uu____2229 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2229  in
          Prims.strcat uu____2228 ")"  in
        Prims.strcat "Rec (" uu____2227

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____2234 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____2234
    | Match (t,uu____2236,uu____2237) ->
        let uu____2260 = t_to_string t  in Prims.strcat "Match " uu____2260

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2262 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2262 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2268 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2268 (FStar_String.concat " ")

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
  'Auu____2459 .
    ('Auu____2459 -> t) ->
      (t -> 'Auu____2459 FStar_Pervasives_Native.option) ->
        t -> 'Auu____2459 embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2510 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____2510 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2530 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkConstruct uu____2530 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____2566  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____2579  -> a)])
  
let (e_any : t embedding) =
  let em a = a  in
  let un t = FStar_Pervasives_Native.Some t  in
  let uu____2603 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____2603 
let (e_unit : unit embedding) =
  let em a = Constant Unit  in
  let un t = FStar_Pervasives_Native.Some ()  in
  let uu____2624 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  mk_emb em un uu____2624 
let (e_bool : Prims.bool embedding) =
  let em a = Constant (Bool a)  in
  let un t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____2650 -> FStar_Pervasives_Native.None  in
  let uu____2651 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  mk_emb em un uu____2651 
let (e_char : FStar_Char.char embedding) =
  let em c = Constant (Char c)  in
  let un c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____2685 -> FStar_Pervasives_Native.None  in
  let uu____2687 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  mk_emb em un uu____2687 
let (e_string : Prims.string embedding) =
  let em s = Constant (String (s, FStar_Range.dummyRange))  in
  let un s =
    match s with
    | Constant (String (s1,uu____2714)) -> FStar_Pervasives_Native.Some s1
    | uu____2715 -> FStar_Pervasives_Native.None  in
  let uu____2716 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  mk_emb em un uu____2716 
let (e_int : FStar_BigInt.t embedding) =
  let em c = Constant (Int c)  in
  let un c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____2742 -> FStar_Pervasives_Native.None  in
  let uu____2743 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  mk_emb em un uu____2743 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____2776 =
            let uu____2777 =
              let uu____2782 = type_of ea  in as_iarg uu____2782  in
            [uu____2777]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____2776
      | FStar_Pervasives_Native.Some x ->
          let uu____2792 =
            let uu____2793 =
              let uu____2798 = type_of ea  in as_iarg uu____2798  in
            let uu____2799 =
              let uu____2806 =
                let uu____2811 = embed ea x  in as_arg uu____2811  in
              [uu____2806]  in
            uu____2793 :: uu____2799  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____2792
       in
    let un trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,uu____2861::(a,uu____2863)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____2890 = unembed ea a  in
          FStar_Util.bind_opt uu____2890
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____2899 -> FStar_Pervasives_Native.None  in
    let uu____2902 =
      let uu____2903 =
        let uu____2904 = let uu____2909 = type_of ea  in as_arg uu____2909
           in
        [uu____2904]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____2903
       in
    mk_emb em un uu____2902
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em x =
        let uu____2968 =
          let uu____2969 = let uu____2974 = type_of ea  in as_iarg uu____2974
             in
          let uu____2975 =
            let uu____2982 =
              let uu____2987 = type_of eb  in as_iarg uu____2987  in
            let uu____2988 =
              let uu____2995 =
                let uu____3000 = embed ea (FStar_Pervasives_Native.fst x)  in
                as_arg uu____3000  in
              let uu____3001 =
                let uu____3008 =
                  let uu____3013 = embed eb (FStar_Pervasives_Native.snd x)
                     in
                  as_arg uu____3013  in
                [uu____3008]  in
              uu____2995 :: uu____3001  in
            uu____2982 :: uu____2988  in
          uu____2969 :: uu____2975  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____2968
         in
      let un trm =
        match trm with
        | Construct
            (fvar1,us,uu____3054::uu____3055::(a,uu____3057)::(b,uu____3059)::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____3098 = unembed ea a  in
            FStar_Util.bind_opt uu____3098
              (fun a1  ->
                 let uu____3108 = unembed eb b  in
                 FStar_Util.bind_opt uu____3108
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____3121 -> FStar_Pervasives_Native.None  in
      let uu____3126 =
        let uu____3127 =
          let uu____3128 = let uu____3133 = type_of ea  in as_arg uu____3133
             in
          let uu____3134 =
            let uu____3141 =
              let uu____3146 = type_of eb  in as_arg uu____3146  in
            [uu____3141]  in
          uu____3128 :: uu____3134  in
        lid_as_typ FStar_Parser_Const.lid_tuple2 [FStar_Syntax_Syntax.U_zero]
          uu____3127
         in
      mk_emb em un uu____3126
  
let (e_range : FStar_Range.range embedding) =
  let em r = Constant (Range r)  in
  let un t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____3184 -> FStar_Pervasives_Native.None  in
  let uu____3185 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  mk_emb em un uu____3185 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em l =
      let typ = let uu____3219 = type_of ea  in as_iarg uu____3219  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____3240 =
          let uu____3241 =
            let uu____3248 =
              let uu____3253 = embed ea hd1  in as_arg uu____3253  in
            let uu____3254 = let uu____3261 = as_arg tl1  in [uu____3261]  in
            uu____3248 :: uu____3254  in
          typ :: uu____3241  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____3240
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un trm =
      match trm with
      | Construct (fv,uu____3297,uu____3298) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____3318,(uu____3319,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____3320))::
           (hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                 )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3349 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3349
            (fun hd2  ->
               let uu____3357 = un tl1  in
               FStar_Util.bind_opt uu____3357
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____3373,(hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3398 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3398
            (fun hd2  ->
               let uu____3406 = un tl1  in
               FStar_Util.bind_opt uu____3406
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____3421 -> FStar_Pervasives_Native.None  in
    let uu____3424 =
      let uu____3425 =
        let uu____3426 = let uu____3431 = type_of ea  in as_arg uu____3431
           in
        [uu____3426]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____3425
       in
    mk_emb em un uu____3424
  
let e_arrow1 : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em f =
        Lam
          ((fun tas  ->
              let uu____3509 =
                let uu____3512 = FStar_List.hd tas  in unembed ea uu____3512
                 in
              match uu____3509 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____3514 = f a  in embed eb uu____3514
              | FStar_Pervasives_Native.None  ->
                  failwith "cannot unembed function argument"),
            [(fun uu____3526  ->
                let uu____3529 = type_of eb  in as_arg uu____3529)],
            (Prims.parse_int "1"))
         in
      let un lam =
        match lam with
        | Lam (ft,uu____3561,uu____3562) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____3602 =
                    let uu____3605 =
                      let uu____3606 =
                        let uu____3609 = embed ea x  in [uu____3609]  in
                      ft uu____3606  in
                    unembed eb uu____3605  in
                  match uu____3602 with
                  | FStar_Pervasives_Native.Some x1 -> x1
                  | FStar_Pervasives_Native.None  ->
                      failwith "cannot unembed function result"))
        | uu____3611 -> FStar_Pervasives_Native.None  in
      let uu____3615 =
        let uu____3616 = type_of ea  in
        let uu____3617 = let uu____3618 = type_of eb  in as_iarg uu____3618
           in
        make_arrow1 uu____3616 uu____3617  in
      mk_emb em un uu____3615
  
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
      let uu____3686 = let uu____3695 = e_list e  in unembed uu____3695  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____3686
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____3716  ->
    match uu____3716 with
    | (a,uu____3724) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____3739)::[]) when
             let uu____3756 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____3756 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____3761 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____3803 = let uu____3810 = as_arg c  in [uu____3810]  in
      int_to_t2 uu____3803
  
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
          let uu____3863 = f a  in FStar_Pervasives_Native.Some uu____3863
      | uu____3864 -> FStar_Pervasives_Native.None
  
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
          let uu____3917 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____3917
      | uu____3918 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____3961 = FStar_List.map as_a args  in lift_unary f uu____3961
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____4015 = FStar_List.map as_a args  in
        lift_binary f uu____4015
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____4044 = f x  in embed e_int uu____4044)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  -> fun y  -> let uu____4070 = f x y  in embed e_int uu____4070)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____4089 = f x  in embed e_bool uu____4089)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  -> fun y  -> let uu____4115 = f x y  in embed e_bool uu____4115)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  -> let uu____4141 = f x y  in embed e_string uu____4141)
  
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
                let uu____4243 =
                  let uu____4252 = as_a a  in
                  let uu____4255 = as_b b  in (uu____4252, uu____4255)  in
                (match uu____4243 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____4270 =
                       let uu____4271 = f a1 b1  in embed_c uu____4271  in
                     FStar_Pervasives_Native.Some uu____4270
                 | uu____4272 -> FStar_Pervasives_Native.None)
            | uu____4281 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____4287 = e_list e_char  in
    let uu____4294 = FStar_String.list_of_string s  in
    embed uu____4287 uu____4294
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____4324 =
        let uu____4325 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____4325  in
      embed e_int uu____4324
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4357 = arg_as_string a1  in
        (match uu____4357 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4363 = arg_as_list e_string a2  in
             (match uu____4363 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____4376 = embed e_string r  in
                  FStar_Pervasives_Native.Some uu____4376
              | uu____4377 -> FStar_Pervasives_Native.None)
         | uu____4382 -> FStar_Pervasives_Native.None)
    | uu____4385 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____4391 = FStar_BigInt.string_of_big_int i  in
    embed e_string uu____4391
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool true  in
      let fal = embed e_bool false  in
      match args with
      | (_univ,uu____4417)::(_typ,uu____4419)::(a1,uu____4421)::(a2,uu____4423)::[]
          ->
          let uu____4444 = eq_t a1 a2  in
          (match uu____4444 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____4449 -> FStar_Pervasives_Native.None)
      | uu____4450 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____4463)::(_typ,uu____4465)::(a1,uu____4467)::(a2,uu____4469)::[]
        ->
        let uu____4490 = eq_t a1 a2  in
        (match uu____4490 with
         | FStar_Syntax_Util.Equal  ->
             let uu____4493 = embed e_bool true  in
             FStar_Pervasives_Native.Some uu____4493
         | FStar_Syntax_Util.NotEqual  ->
             let uu____4494 = embed e_bool false  in
             FStar_Pervasives_Native.Some uu____4494
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____4495 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____4512 =
        let uu____4513 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____4513  in
      failwith uu____4512
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____4526)::[] ->
        let uu____4535 = unembed e_range a1  in
        (match uu____4535 with
         | FStar_Pervasives_Native.Some r ->
             let uu____4541 = embed e_range r  in
             FStar_Pervasives_Native.Some uu____4541
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____4542 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4576 = arg_as_list e_char a1  in
        (match uu____4576 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4592 = arg_as_string a2  in
             (match uu____4592 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____4601 =
                    let uu____4602 = e_list e_string  in embed uu____4602 r
                     in
                  FStar_Pervasives_Native.Some uu____4601
              | uu____4609 -> FStar_Pervasives_Native.None)
         | uu____4612 -> FStar_Pervasives_Native.None)
    | uu____4618 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____4659 =
          let uu____4672 = arg_as_string a1  in
          let uu____4675 = arg_as_int a2  in
          let uu____4678 = arg_as_int a3  in
          (uu____4672, uu____4675, uu____4678)  in
        (match uu____4659 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                let r = FStar_String.substring s1 n11 n21  in
                let uu____4709 = embed e_string r  in
                FStar_Pervasives_Native.Some uu____4709
              with | uu____4715 -> FStar_Pervasives_Native.None)
         | uu____4716 -> FStar_Pervasives_Native.None)
    | uu____4729 -> FStar_Pervasives_Native.None
  