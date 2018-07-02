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
                 Prims.list,Prims.int,t Prims.list ->
                                        FStar_Syntax_Syntax.letbinding -> t)
  FStar_Pervasives_Native.tuple6 
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
    match projectee with | Var _0 -> true | uu____419 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____450 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____537 -> false
  
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
    match projectee with | Accu _0 -> true | uu____627 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____685 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____755 -> false 
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
    match projectee with | Constant _0 -> true | uu____811 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____825 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____839 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____852 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____879 -> false
  
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
    match projectee with | Refinement _0 -> true | uu____967 -> false
  
let (__proj__Refinement__item___0 :
  t ->
    (t -> t,unit ->
              (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1027 -> false
  
let (__proj__Quote__item___0 :
  t ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1053 -> false
  
let (__proj__Lazy__item___0 : t -> FStar_Syntax_Syntax.lazyinfo) =
  fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1097 -> false
  
let (__proj__Rec__item___0 :
  t ->
    (FStar_Syntax_Syntax.letbinding,FStar_Syntax_Syntax.letbinding Prims.list,
      t Prims.list,(t,FStar_Syntax_Syntax.aqual)
                     FStar_Pervasives_Native.tuple2 Prims.list,Prims.int,
      t Prims.list -> FStar_Syntax_Syntax.letbinding -> t)
      FStar_Pervasives_Native.tuple6)
  = fun projectee  -> match projectee with | Rec _0 -> _0 
let (uu___is_Tot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Tot _0 -> true | uu____1207 -> false
  
let (__proj__Tot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1245 -> false
  
let (__proj__GTot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1277 -> false
  
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
  fun trm  -> match trm with | Accu uu____1408 -> true | uu____1419 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1425,uu____1426) -> false | uu____1439 -> true
  
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
  fun uu___226_1568  ->
    if uu___226_1568
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___227_1574  ->
    if uu___227_1574
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
      | (FStar_Syntax_Util.NotEqual ,uu____1586) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1587,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1588) -> FStar_Syntax_Util.Unknown
      | (uu____1589,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1605 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1621),String (s2,uu____1623)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1631,uu____1632) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1667,Lam uu____1668) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____1741 = eq_atom a1 a2  in
          eq_and uu____1741 (fun uu____1743  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____1782 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1782
          then
            let uu____1783 =
              let uu____1784 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1784  in
            eq_and uu____1783 (fun uu____1786  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____1826 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1826
          then
            let uu____1827 =
              let uu____1828 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1828  in
            eq_and uu____1827 (fun uu____1830  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____1836 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1836
      | (Univ u1,Univ u2) ->
          let uu____1839 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1839
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____1885 =
            let uu____1886 =
              let uu____1887 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1887  in
            let uu____1892 =
              let uu____1893 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1893  in
            eq_t uu____1886 uu____1892  in
          eq_and uu____1885
            (fun uu____1901  ->
               let uu____1902 =
                 let uu____1903 = mkAccuVar x  in r1 uu____1903  in
               let uu____1904 =
                 let uu____1905 = mkAccuVar x  in r2 uu____1905  in
               eq_t uu____1902 uu____1904)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____1906,uu____1907) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____1912,uu____1913) -> FStar_Syntax_Util.Unknown

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
          let uu____1994 = eq_arg x y  in
          eq_and uu____1994 (fun uu____1996  -> eq_args xs ys)
      | (uu____1997,uu____1998) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2034) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2036 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2036
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity) ->
        let uu____2089 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2099 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____2089 uu____2099
    | Accu (a,l) ->
        let uu____2114 =
          let uu____2115 = atom_to_string a  in
          let uu____2116 =
            let uu____2117 =
              let uu____2118 =
                let uu____2119 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2119  in
              Prims.strcat uu____2118 ")"  in
            Prims.strcat ") (" uu____2117  in
          Prims.strcat uu____2115 uu____2116  in
        Prims.strcat "Accu (" uu____2114
    | Construct (fv,us,l) ->
        let uu____2151 =
          let uu____2152 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2153 =
            let uu____2154 =
              let uu____2155 =
                let uu____2156 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2156  in
              let uu____2159 =
                let uu____2160 =
                  let uu____2161 =
                    let uu____2162 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2162  in
                  Prims.strcat uu____2161 "]"  in
                Prims.strcat "] [" uu____2160  in
              Prims.strcat uu____2155 uu____2159  in
            Prims.strcat ") [" uu____2154  in
          Prims.strcat uu____2152 uu____2153  in
        Prims.strcat "Construct (" uu____2151
    | FV (fv,us,l) ->
        let uu____2194 =
          let uu____2195 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2196 =
            let uu____2197 =
              let uu____2198 =
                let uu____2199 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2199  in
              let uu____2202 =
                let uu____2203 =
                  let uu____2204 =
                    let uu____2205 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2205  in
                  Prims.strcat uu____2204 "]"  in
                Prims.strcat "] [" uu____2203  in
              Prims.strcat uu____2198 uu____2202  in
            Prims.strcat ") [" uu____2197  in
          Prims.strcat uu____2195 uu____2196  in
        Prims.strcat "FV (" uu____2194
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2220 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____2220
    | Type_t u ->
        let uu____2222 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____2222
    | Arrow uu____2223 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____2268 = t ()  in FStar_Pervasives_Native.fst uu____2268
           in
        let uu____2273 =
          let uu____2274 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____2275 =
            let uu____2276 =
              let uu____2277 = t_to_string t1  in
              let uu____2278 =
                let uu____2279 =
                  let uu____2280 =
                    let uu____2281 =
                      let uu____2282 = mkAccuVar x1  in f uu____2282  in
                    t_to_string uu____2281  in
                  Prims.strcat uu____2280 "}"  in
                Prims.strcat "{" uu____2279  in
              Prims.strcat uu____2277 uu____2278  in
            Prims.strcat ":" uu____2276  in
          Prims.strcat uu____2274 uu____2275  in
        Prims.strcat "Refinement " uu____2273
    | Unknown  -> "Unknown"
    | Quote uu____2283 -> "Quote _"
    | Lazy uu____2288 -> "Lazy _"
    | Rec (uu____2289,uu____2290,l,uu____2292,uu____2293,uu____2294) ->
        let uu____2331 =
          let uu____2332 =
            let uu____2333 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2333  in
          Prims.strcat uu____2332 ")"  in
        Prims.strcat "Rec (" uu____2331

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____2338 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____2338
    | Match (t,uu____2340,uu____2341) ->
        let uu____2364 = t_to_string t  in Prims.strcat "Match " uu____2364

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2366 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2366 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2372 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2372 (FStar_String.concat " ")

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
  'a .
    ('a -> t) ->
      (t -> 'a FStar_Pervasives_Native.option) -> t -> 'a embedding
  = fun em  -> fun un  -> fun typ  -> { em; un; typ } 
let (lid_as_constr :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2614 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____2614 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2634 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkConstruct uu____2634 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____2672  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____2687  -> a)])
  
let (e_any : t embedding) =
  let em a = a  in
  let un t = FStar_Pervasives_Native.Some t  in
  let uu____2717 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____2717 
let (e_unit : unit embedding) =
  let em a = Constant Unit  in
  let un t = FStar_Pervasives_Native.Some ()  in
  let uu____2740 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  mk_emb em un uu____2740 
let (e_bool : Prims.bool embedding) =
  let em a = Constant (Bool a)  in
  let un t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____2766 -> FStar_Pervasives_Native.None  in
  let uu____2767 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  mk_emb em un uu____2767 
let (e_char : FStar_Char.char embedding) =
  let em c = Constant (Char c)  in
  let un c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____2801 -> FStar_Pervasives_Native.None  in
  let uu____2803 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  mk_emb em un uu____2803 
let (e_string : Prims.string embedding) =
  let em s = Constant (String (s, FStar_Range.dummyRange))  in
  let un s =
    match s with
    | Constant (String (s1,uu____2830)) -> FStar_Pervasives_Native.Some s1
    | uu____2831 -> FStar_Pervasives_Native.None  in
  let uu____2832 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  mk_emb em un uu____2832 
let (e_int : FStar_BigInt.t embedding) =
  let em c = Constant (Int c)  in
  let un c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____2858 -> FStar_Pervasives_Native.None  in
  let uu____2859 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  mk_emb em un uu____2859 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____2892 =
            let uu____2893 =
              let uu____2898 = type_of ea  in as_iarg uu____2898  in
            [uu____2893]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____2892
      | FStar_Pervasives_Native.Some x ->
          let uu____2908 =
            let uu____2909 =
              let uu____2914 = type_of ea  in as_iarg uu____2914  in
            let uu____2915 =
              let uu____2922 =
                let uu____2927 = embed ea x  in as_arg uu____2927  in
              [uu____2922]  in
            uu____2909 :: uu____2915  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____2908
       in
    let un trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,uu____2977::(a,uu____2979)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____3006 = unembed ea a  in
          FStar_Util.bind_opt uu____3006
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____3015 -> FStar_Pervasives_Native.None  in
    let uu____3018 =
      let uu____3019 =
        let uu____3020 = let uu____3025 = type_of ea  in as_arg uu____3025
           in
        [uu____3020]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____3019
       in
    mk_emb em un uu____3018
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em x =
        let uu____3084 =
          let uu____3085 = let uu____3090 = type_of ea  in as_iarg uu____3090
             in
          let uu____3091 =
            let uu____3098 =
              let uu____3103 = type_of eb  in as_iarg uu____3103  in
            let uu____3104 =
              let uu____3111 =
                let uu____3116 = embed ea (FStar_Pervasives_Native.fst x)  in
                as_arg uu____3116  in
              let uu____3117 =
                let uu____3124 =
                  let uu____3129 = embed eb (FStar_Pervasives_Native.snd x)
                     in
                  as_arg uu____3129  in
                [uu____3124]  in
              uu____3111 :: uu____3117  in
            uu____3098 :: uu____3104  in
          uu____3085 :: uu____3091  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____3084
         in
      let un trm =
        match trm with
        | Construct
            (fvar1,us,uu____3170::uu____3171::(a,uu____3173)::(b,uu____3175)::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____3214 = unembed ea a  in
            FStar_Util.bind_opt uu____3214
              (fun a1  ->
                 let uu____3224 = unembed eb b  in
                 FStar_Util.bind_opt uu____3224
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____3237 -> FStar_Pervasives_Native.None  in
      let uu____3242 =
        let uu____3243 =
          let uu____3244 = let uu____3249 = type_of ea  in as_arg uu____3249
             in
          let uu____3250 =
            let uu____3257 =
              let uu____3262 = type_of eb  in as_arg uu____3262  in
            [uu____3257]  in
          uu____3244 :: uu____3250  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____3243
         in
      mk_emb em un uu____3242
  
let (e_range : FStar_Range.range embedding) =
  let em r = Constant (Range r)  in
  let un t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____3300 -> FStar_Pervasives_Native.None  in
  let uu____3301 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  mk_emb em un uu____3301 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em l =
      let typ = let uu____3335 = type_of ea  in as_iarg uu____3335  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____3356 =
          let uu____3357 =
            let uu____3364 =
              let uu____3369 = embed ea hd1  in as_arg uu____3369  in
            let uu____3370 = let uu____3377 = as_arg tl1  in [uu____3377]  in
            uu____3364 :: uu____3370  in
          typ :: uu____3357  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____3356
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un trm =
      match trm with
      | Construct (fv,uu____3413,uu____3414) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____3434,(uu____3435,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____3436))::
           (hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                 )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3465 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3465
            (fun hd2  ->
               let uu____3473 = un tl1  in
               FStar_Util.bind_opt uu____3473
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____3489,(hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3514 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3514
            (fun hd2  ->
               let uu____3522 = un tl1  in
               FStar_Util.bind_opt uu____3522
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____3537 -> FStar_Pervasives_Native.None  in
    let uu____3540 =
      let uu____3541 =
        let uu____3542 = let uu____3547 = type_of ea  in as_arg uu____3547
           in
        [uu____3542]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____3541
       in
    mk_emb em un uu____3540
  
let e_arrow1 : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em f =
        Lam
          ((fun tas  ->
              let uu____3625 =
                let uu____3628 = FStar_List.hd tas  in unembed ea uu____3628
                 in
              match uu____3625 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____3630 = f a  in embed eb uu____3630
              | FStar_Pervasives_Native.None  ->
                  failwith "cannot unembed function argument"),
            [(fun uu____3642  ->
                let uu____3645 = type_of eb  in as_arg uu____3645)],
            (Prims.parse_int "1"))
         in
      let un lam =
        match lam with
        | Lam (ft,uu____3677,uu____3678) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____3718 =
                    let uu____3721 =
                      let uu____3722 =
                        let uu____3725 = embed ea x  in [uu____3725]  in
                      ft uu____3722  in
                    unembed eb uu____3721  in
                  match uu____3718 with
                  | FStar_Pervasives_Native.Some x1 -> x1
                  | FStar_Pervasives_Native.None  ->
                      failwith "cannot unembed function result"))
        | uu____3727 -> FStar_Pervasives_Native.None  in
      let uu____3731 =
        let uu____3732 = type_of ea  in
        let uu____3733 = let uu____3734 = type_of eb  in as_iarg uu____3734
           in
        make_arrow1 uu____3732 uu____3733  in
      mk_emb em un uu____3731
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____3746 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3746 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____3751 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3751 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____3756 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3756 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____3761 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3761 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____3766 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3766 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____3771 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3771 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____3776 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3776 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____3781 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3781 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____3786 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3786 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____3794 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____3795 =
          let uu____3796 =
            let uu____3801 =
              let uu____3802 = e_list e_string  in embed uu____3802 l  in
            as_arg uu____3801  in
          [uu____3796]  in
        mkFV uu____3794 [] uu____3795
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____3820 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____3821 =
          let uu____3822 =
            let uu____3827 =
              let uu____3828 = e_list e_string  in embed uu____3828 l  in
            as_arg uu____3827  in
          [uu____3822]  in
        mkFV uu____3820 [] uu____3821
    | FStar_Syntax_Embeddings.UnfoldAttr a -> failwith "NBE UnfoldAttr..."
     in
  let un t0 =
    match t0 with
    | FV (fv,uu____3855,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____3871,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____3887,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____3903,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____3919,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____3935,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____3951,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____3967,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____3983,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____3999,(l,uu____4001)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____4020 =
          let uu____4025 = e_list e_string  in unembed uu____4025 l  in
        FStar_Util.bind_opt uu____4020
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____4041,(l,uu____4043)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____4062 =
          let uu____4067 = e_list e_string  in unembed uu____4067 l  in
        FStar_Util.bind_opt uu____4062
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | uu____4082 ->
        ((let uu____4084 =
            let uu____4089 =
              let uu____4090 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____4090
               in
            (FStar_Errors.Warning_NotEmbedded, uu____4089)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4084);
         FStar_Pervasives_Native.None)
     in
  let uu____4091 =
    let uu____4092 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____4092 [] []  in
  mk_emb em un uu____4091 
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
      let uu____4161 = let uu____4170 = e_list e  in unembed uu____4170  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4161
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____4191  ->
    match uu____4191 with
    | (a,uu____4199) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____4214)::[]) when
             let uu____4231 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____4231 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____4236 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____4278 = let uu____4285 = as_arg c  in [uu____4285]  in
      int_to_t2 uu____4278
  
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
          let uu____4338 = f a  in FStar_Pervasives_Native.Some uu____4338
      | uu____4339 -> FStar_Pervasives_Native.None
  
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
          let uu____4392 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____4392
      | uu____4393 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____4436 = FStar_List.map as_a args  in lift_unary f uu____4436
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____4490 = FStar_List.map as_a args  in
        lift_binary f uu____4490
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____4519 = f x  in embed e_int uu____4519)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  -> fun y  -> let uu____4545 = f x y  in embed e_int uu____4545)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____4564 = f x  in embed e_bool uu____4564)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  -> fun y  -> let uu____4590 = f x y  in embed e_bool uu____4590)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  -> let uu____4616 = f x y  in embed e_string uu____4616)
  
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
                let uu____4718 =
                  let uu____4727 = as_a a  in
                  let uu____4730 = as_b b  in (uu____4727, uu____4730)  in
                (match uu____4718 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____4745 =
                       let uu____4746 = f a1 b1  in embed_c uu____4746  in
                     FStar_Pervasives_Native.Some uu____4745
                 | uu____4747 -> FStar_Pervasives_Native.None)
            | uu____4756 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____4762 = e_list e_char  in
    let uu____4769 = FStar_String.list_of_string s  in
    embed uu____4762 uu____4769
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____4799 =
        let uu____4800 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____4800  in
      embed e_int uu____4799
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4832 = arg_as_string a1  in
        (match uu____4832 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4838 = arg_as_list e_string a2  in
             (match uu____4838 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____4851 = embed e_string r  in
                  FStar_Pervasives_Native.Some uu____4851
              | uu____4852 -> FStar_Pervasives_Native.None)
         | uu____4857 -> FStar_Pervasives_Native.None)
    | uu____4860 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____4866 = FStar_BigInt.string_of_big_int i  in
    embed e_string uu____4866
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool true  in
      let fal = embed e_bool false  in
      match args with
      | (_univ,uu____4892)::(_typ,uu____4894)::(a1,uu____4896)::(a2,uu____4898)::[]
          ->
          let uu____4919 = eq_t a1 a2  in
          (match uu____4919 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____4924 -> FStar_Pervasives_Native.None)
      | uu____4925 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____4938)::(_typ,uu____4940)::(a1,uu____4942)::(a2,uu____4944)::[]
        ->
        let uu____4965 = eq_t a1 a2  in
        (match uu____4965 with
         | FStar_Syntax_Util.Equal  ->
             let uu____4968 = embed e_bool true  in
             FStar_Pervasives_Native.Some uu____4968
         | FStar_Syntax_Util.NotEqual  ->
             let uu____4969 = embed e_bool false  in
             FStar_Pervasives_Native.Some uu____4969
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____4970 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____4987 =
        let uu____4988 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____4988  in
      failwith uu____4987
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____5001)::[] ->
        let uu____5010 = unembed e_range a1  in
        (match uu____5010 with
         | FStar_Pervasives_Native.Some r ->
             let uu____5016 = embed e_range r  in
             FStar_Pervasives_Native.Some uu____5016
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____5017 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____5051 = arg_as_list e_char a1  in
        (match uu____5051 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5067 = arg_as_string a2  in
             (match uu____5067 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____5076 =
                    let uu____5077 = e_list e_string  in embed uu____5077 r
                     in
                  FStar_Pervasives_Native.Some uu____5076
              | uu____5084 -> FStar_Pervasives_Native.None)
         | uu____5087 -> FStar_Pervasives_Native.None)
    | uu____5093 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____5134 =
          let uu____5147 = arg_as_string a1  in
          let uu____5150 = arg_as_int a2  in
          let uu____5153 = arg_as_int a3  in
          (uu____5147, uu____5150, uu____5153)  in
        (match uu____5134 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                (fun uu___229_5180  ->
                   match () with
                   | () ->
                       let r = FStar_String.substring s1 n11 n21  in
                       let uu____5184 = embed e_string r  in
                       FStar_Pervasives_Native.Some uu____5184) ()
              with | uu____5190 -> FStar_Pervasives_Native.None)
         | uu____5191 -> FStar_Pervasives_Native.None)
    | uu____5204 -> FStar_Pervasives_Native.None
  