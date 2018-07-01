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
    match projectee with | Var _0 -> true | uu____417 -> false
  
let (__proj__Var__item___0 : atom -> var) =
  fun projectee  -> match projectee with | Var _0 -> _0 
let (uu___is_Match : atom -> Prims.bool) =
  fun projectee  ->
    match projectee with | Match _0 -> true | uu____448 -> false
  
let (__proj__Match__item___0 :
  atom ->
    (t,t -> t,(t -> FStar_Syntax_Syntax.term) ->
                FStar_Syntax_Syntax.branch Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Match _0 -> _0 
let (uu___is_Lam : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lam _0 -> true | uu____535 -> false
  
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
    match projectee with | Accu _0 -> true | uu____625 -> false
  
let (__proj__Accu__item___0 :
  t ->
    (atom,(t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2
            Prims.list)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Accu _0 -> _0 
let (uu___is_Construct : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Construct _0 -> true | uu____683 -> false
  
let (__proj__Construct__item___0 :
  t ->
    (FStar_Syntax_Syntax.fv,FStar_Syntax_Syntax.universe Prims.list,(t,
                                                                    FStar_Syntax_Syntax.aqual)
                                                                    FStar_Pervasives_Native.tuple2
                                                                    Prims.list)
      FStar_Pervasives_Native.tuple3)
  = fun projectee  -> match projectee with | Construct _0 -> _0 
let (uu___is_FV : t -> Prims.bool) =
  fun projectee  -> match projectee with | FV _0 -> true | uu____753 -> false 
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
    match projectee with | Constant _0 -> true | uu____809 -> false
  
let (__proj__Constant__item___0 : t -> constant) =
  fun projectee  -> match projectee with | Constant _0 -> _0 
let (uu___is_Type_t : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Type_t _0 -> true | uu____823 -> false
  
let (__proj__Type_t__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Type_t _0 -> _0 
let (uu___is_Univ : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Univ _0 -> true | uu____837 -> false
  
let (__proj__Univ__item___0 : t -> FStar_Syntax_Syntax.universe) =
  fun projectee  -> match projectee with | Univ _0 -> _0 
let (uu___is_Unknown : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Unknown  -> true | uu____850 -> false
  
let (uu___is_Arrow : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Arrow _0 -> true | uu____875 -> false
  
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
    match projectee with | Refinement _0 -> true | uu____957 -> false
  
let (__proj__Refinement__item___0 :
  t ->
    (t -> t,unit ->
              (t,FStar_Syntax_Syntax.aqual) FStar_Pervasives_Native.tuple2)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Refinement _0 -> _0 
let (uu___is_Quote : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Quote _0 -> true | uu____1017 -> false
  
let (__proj__Quote__item___0 :
  t ->
    (FStar_Syntax_Syntax.term,FStar_Syntax_Syntax.quoteinfo)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Quote _0 -> _0 
let (uu___is_Lazy : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Lazy _0 -> true | uu____1043 -> false
  
let (__proj__Lazy__item___0 : t -> FStar_Syntax_Syntax.lazyinfo) =
  fun projectee  -> match projectee with | Lazy _0 -> _0 
let (uu___is_Rec : t -> Prims.bool) =
  fun projectee  ->
    match projectee with | Rec _0 -> true | uu____1087 -> false
  
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
    match projectee with | Tot _0 -> true | uu____1197 -> false
  
let (__proj__Tot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Tot _0 -> _0 
let (uu___is_GTot : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | GTot _0 -> true | uu____1235 -> false
  
let (__proj__GTot__item___0 :
  comp ->
    (t,FStar_Syntax_Syntax.universe FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | GTot _0 -> _0 
let (uu___is_Comp : comp -> Prims.bool) =
  fun projectee  ->
    match projectee with | Comp _0 -> true | uu____1267 -> false
  
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
  fun trm  -> match trm with | Accu uu____1398 -> true | uu____1409 -> false 
let (isNotAccu : t -> Prims.bool) =
  fun x  ->
    match x with | Accu (uu____1415,uu____1416) -> false | uu____1429 -> true
  
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
  fun uu___222_1558  ->
    if uu___222_1558
    then FStar_Syntax_Util.Equal
    else FStar_Syntax_Util.Unknown
  
let (equal_iff : Prims.bool -> FStar_Syntax_Util.eq_result) =
  fun uu___223_1564  ->
    if uu___223_1564
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
      | (FStar_Syntax_Util.NotEqual ,uu____1576) ->
          FStar_Syntax_Util.NotEqual
      | (uu____1577,FStar_Syntax_Util.NotEqual ) ->
          FStar_Syntax_Util.NotEqual
      | (FStar_Syntax_Util.Unknown ,uu____1578) -> FStar_Syntax_Util.Unknown
      | (uu____1579,FStar_Syntax_Util.Unknown ) -> FStar_Syntax_Util.Unknown
  
let (eq_and :
  FStar_Syntax_Util.eq_result ->
    (unit -> FStar_Syntax_Util.eq_result) -> FStar_Syntax_Util.eq_result)
  =
  fun f  ->
    fun g  ->
      match f with
      | FStar_Syntax_Util.Equal  -> g ()
      | uu____1595 -> FStar_Syntax_Util.Unknown
  
let (eq_constant : constant -> constant -> FStar_Syntax_Util.eq_result) =
  fun c1  ->
    fun c2  ->
      match (c1, c2) with
      | (Unit ,Unit ) -> FStar_Syntax_Util.Equal
      | (Bool b1,Bool b2) -> equal_iff (b1 = b2)
      | (Int i1,Int i2) -> equal_iff (i1 = i2)
      | (String (s1,uu____1611),String (s2,uu____1613)) ->
          equal_iff (s1 = s2)
      | (Char c11,Char c21) -> equal_iff (c11 = c21)
      | (Range r1,Range r2) -> FStar_Syntax_Util.Unknown
      | (uu____1621,uu____1622) -> FStar_Syntax_Util.NotEqual
  
let rec (eq_t : t -> t -> FStar_Syntax_Util.eq_result) =
  fun t1  ->
    fun t2  ->
      match (t1, t2) with
      | (Lam uu____1657,Lam uu____1658) -> FStar_Syntax_Util.Unknown
      | (Accu (a1,as1),Accu (a2,as2)) ->
          let uu____1731 = eq_atom a1 a2  in
          eq_and uu____1731 (fun uu____1733  -> eq_args as1 as2)
      | (Construct (v1,us1,args1),Construct (v2,us2,args2)) ->
          let uu____1772 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1772
          then
            let uu____1773 =
              let uu____1774 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1774  in
            eq_and uu____1773 (fun uu____1776  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (FV (v1,us1,args1),FV (v2,us2,args2)) ->
          let uu____1816 = FStar_Syntax_Syntax.fv_eq v1 v2  in
          if uu____1816
          then
            let uu____1817 =
              let uu____1818 = FStar_Syntax_Util.eq_univs_list us1 us2  in
              equal_iff uu____1818  in
            eq_and uu____1817 (fun uu____1820  -> eq_args args1 args2)
          else FStar_Syntax_Util.NotEqual
      | (Constant c1,Constant c2) -> eq_constant c1 c2
      | (Type_t u1,Type_t u2) ->
          let uu____1826 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1826
      | (Univ u1,Univ u2) ->
          let uu____1829 = FStar_Syntax_Util.eq_univs u1 u2  in
          equal_iff uu____1829
      | (Refinement (r1,t11),Refinement (r2,t21)) ->
          let x =
            FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
              FStar_Syntax_Syntax.t_unit
             in
          let uu____1875 =
            let uu____1876 =
              let uu____1877 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1877  in
            let uu____1882 =
              let uu____1883 = t11 ()  in
              FStar_Pervasives_Native.fst uu____1883  in
            eq_t uu____1876 uu____1882  in
          eq_and uu____1875
            (fun uu____1891  ->
               let uu____1892 =
                 let uu____1893 = mkAccuVar x  in r1 uu____1893  in
               let uu____1894 =
                 let uu____1895 = mkAccuVar x  in r2 uu____1895  in
               eq_t uu____1892 uu____1894)
      | (Unknown ,Unknown ) -> FStar_Syntax_Util.Equal
      | (uu____1896,uu____1897) -> FStar_Syntax_Util.Unknown

and (eq_atom : atom -> atom -> FStar_Syntax_Util.eq_result) =
  fun a1  ->
    fun a2  ->
      match (a1, a2) with
      | (Var bv1,Var bv2) -> equal_if (FStar_Syntax_Syntax.bv_eq bv1 bv2)
      | (uu____1902,uu____1903) -> FStar_Syntax_Util.Unknown

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
          let uu____1984 = eq_arg x y  in
          eq_and uu____1984 (fun uu____1986  -> eq_args xs ys)
      | (uu____1987,uu____1988) -> FStar_Syntax_Util.Unknown

let (constant_to_string : constant -> Prims.string) =
  fun c  ->
    match c with
    | Unit  -> "Unit"
    | Bool b -> if b then "Bool true" else "Bool false"
    | Int i -> FStar_BigInt.string_of_big_int i
    | Char c1 -> FStar_Util.format1 "'%s'" (FStar_Util.string_of_char c1)
    | String (s,uu____2024) -> FStar_Util.format1 "\"%s\"" s
    | Range r ->
        let uu____2026 = FStar_Range.string_of_range r  in
        FStar_Util.format1 "Range %s" uu____2026
  
let rec (t_to_string : t -> Prims.string) =
  fun x  ->
    match x with
    | Lam (b,args,arity) ->
        let uu____2079 = FStar_Util.string_of_int (FStar_List.length args)
           in
        let uu____2089 = FStar_Util.string_of_int arity  in
        FStar_Util.format2 "Lam (_, %s args, %s)" uu____2079 uu____2089
    | Accu (a,l) ->
        let uu____2104 =
          let uu____2105 = atom_to_string a  in
          let uu____2106 =
            let uu____2107 =
              let uu____2108 =
                let uu____2109 =
                  FStar_List.map
                    (fun x1  -> t_to_string (FStar_Pervasives_Native.fst x1))
                    l
                   in
                FStar_String.concat "; " uu____2109  in
              Prims.strcat uu____2108 ")"  in
            Prims.strcat ") (" uu____2107  in
          Prims.strcat uu____2105 uu____2106  in
        Prims.strcat "Accu (" uu____2104
    | Construct (fv,us,l) ->
        let uu____2141 =
          let uu____2142 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2143 =
            let uu____2144 =
              let uu____2145 =
                let uu____2146 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2146  in
              let uu____2149 =
                let uu____2150 =
                  let uu____2151 =
                    let uu____2152 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2152  in
                  Prims.strcat uu____2151 "]"  in
                Prims.strcat "] [" uu____2150  in
              Prims.strcat uu____2145 uu____2149  in
            Prims.strcat ") [" uu____2144  in
          Prims.strcat uu____2142 uu____2143  in
        Prims.strcat "Construct (" uu____2141
    | FV (fv,us,l) ->
        let uu____2184 =
          let uu____2185 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____2186 =
            let uu____2187 =
              let uu____2188 =
                let uu____2189 =
                  FStar_List.map FStar_Syntax_Print.univ_to_string us  in
                FStar_String.concat "; " uu____2189  in
              let uu____2192 =
                let uu____2193 =
                  let uu____2194 =
                    let uu____2195 =
                      FStar_List.map
                        (fun x1  ->
                           t_to_string (FStar_Pervasives_Native.fst x1)) l
                       in
                    FStar_String.concat "; " uu____2195  in
                  Prims.strcat uu____2194 "]"  in
                Prims.strcat "] [" uu____2193  in
              Prims.strcat uu____2188 uu____2192  in
            Prims.strcat ") [" uu____2187  in
          Prims.strcat uu____2185 uu____2186  in
        Prims.strcat "FV (" uu____2184
    | Constant c -> constant_to_string c
    | Univ u ->
        let uu____2210 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Universe " uu____2210
    | Type_t u ->
        let uu____2212 = FStar_Syntax_Print.univ_to_string u  in
        Prims.strcat "Type_t " uu____2212
    | Arrow uu____2213 -> "Arrow"
    | Refinement (f,t) ->
        let x1 =
          FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
            FStar_Syntax_Syntax.t_unit
           in
        let t1 =
          let uu____2256 = t ()  in FStar_Pervasives_Native.fst uu____2256
           in
        let uu____2261 =
          let uu____2262 = FStar_Syntax_Print.bv_to_string x1  in
          let uu____2263 =
            let uu____2264 =
              let uu____2265 = t_to_string t1  in
              let uu____2266 =
                let uu____2267 =
                  let uu____2268 =
                    let uu____2269 =
                      let uu____2270 = mkAccuVar x1  in f uu____2270  in
                    t_to_string uu____2269  in
                  Prims.strcat uu____2268 "}"  in
                Prims.strcat "{" uu____2267  in
              Prims.strcat uu____2265 uu____2266  in
            Prims.strcat ":" uu____2264  in
          Prims.strcat uu____2262 uu____2263  in
        Prims.strcat "Refinement " uu____2261
    | Unknown  -> "Unknown"
    | Quote uu____2271 -> "Quote _"
    | Lazy uu____2276 -> "Lazy _"
    | Rec (uu____2277,uu____2278,l,uu____2280,uu____2281,uu____2282) ->
        let uu____2319 =
          let uu____2320 =
            let uu____2321 = FStar_List.map t_to_string l  in
            FStar_String.concat "; " uu____2321  in
          Prims.strcat uu____2320 ")"  in
        Prims.strcat "Rec (" uu____2319

and (atom_to_string : atom -> Prims.string) =
  fun a  ->
    match a with
    | Var v1 ->
        let uu____2326 = FStar_Syntax_Print.bv_to_string v1  in
        Prims.strcat "Var " uu____2326
    | Match (t,uu____2328,uu____2329) ->
        let uu____2352 = t_to_string t  in Prims.strcat "Match " uu____2352

and (arg_to_string : arg -> Prims.string) =
  fun a  ->
    let uu____2354 = FStar_All.pipe_right a FStar_Pervasives_Native.fst  in
    FStar_All.pipe_right uu____2354 t_to_string

and (args_to_string : args -> Prims.string) =
  fun args  ->
    let uu____2360 = FStar_All.pipe_right args (FStar_List.map arg_to_string)
       in
    FStar_All.pipe_right uu____2360 (FStar_String.concat " ")

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
        let uu____2602 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.Data_ctor)
           in
        mkConstruct uu____2602 us args
  
let (lid_as_typ :
  FStar_Ident.lident -> FStar_Syntax_Syntax.universe Prims.list -> args -> t)
  =
  fun l  ->
    fun us  ->
      fun args  ->
        let uu____2622 =
          FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
            FStar_Pervasives_Native.None
           in
        mkConstruct uu____2622 us args
  
let (as_iarg : t -> arg) =
  fun a  -> (a, (FStar_Pervasives_Native.Some FStar_Syntax_Syntax.imp_tag)) 
let (as_arg : t -> arg) = fun a  -> (a, FStar_Pervasives_Native.None) 
let (make_arrow1 : t -> arg -> t) =
  fun t1  ->
    fun a  ->
      Arrow
        ((fun uu____2658  -> Tot (t1, FStar_Pervasives_Native.None)),
          [(fun uu____2671  -> a)])
  
let (e_any : t embedding) =
  let em a = a  in
  let un t = FStar_Pervasives_Native.Some t  in
  let uu____2697 = lid_as_typ FStar_Parser_Const.term_lid [] []  in
  mk_emb em un uu____2697 
let (e_unit : unit embedding) =
  let em a = Constant Unit  in
  let un t = FStar_Pervasives_Native.Some ()  in
  let uu____2720 = lid_as_typ FStar_Parser_Const.unit_lid [] []  in
  mk_emb em un uu____2720 
let (e_bool : Prims.bool embedding) =
  let em a = Constant (Bool a)  in
  let un t =
    match t with
    | Constant (Bool a) -> FStar_Pervasives_Native.Some a
    | uu____2746 -> FStar_Pervasives_Native.None  in
  let uu____2747 = lid_as_typ FStar_Parser_Const.bool_lid [] []  in
  mk_emb em un uu____2747 
let (e_char : FStar_Char.char embedding) =
  let em c = Constant (Char c)  in
  let un c =
    match c with
    | Constant (Char a) -> FStar_Pervasives_Native.Some a
    | uu____2781 -> FStar_Pervasives_Native.None  in
  let uu____2783 = lid_as_typ FStar_Parser_Const.char_lid [] []  in
  mk_emb em un uu____2783 
let (e_string : Prims.string embedding) =
  let em s = Constant (String (s, FStar_Range.dummyRange))  in
  let un s =
    match s with
    | Constant (String (s1,uu____2810)) -> FStar_Pervasives_Native.Some s1
    | uu____2811 -> FStar_Pervasives_Native.None  in
  let uu____2812 = lid_as_typ FStar_Parser_Const.string_lid [] []  in
  mk_emb em un uu____2812 
let (e_int : FStar_BigInt.t embedding) =
  let em c = Constant (Int c)  in
  let un c =
    match c with
    | Constant (Int a) -> FStar_Pervasives_Native.Some a
    | uu____2838 -> FStar_Pervasives_Native.None  in
  let uu____2839 = lid_as_typ FStar_Parser_Const.int_lid [] []  in
  mk_emb em un uu____2839 
let e_option :
  'a . 'a embedding -> 'a FStar_Pervasives_Native.option embedding =
  fun ea  ->
    let em o =
      match o with
      | FStar_Pervasives_Native.None  ->
          let uu____2872 =
            let uu____2873 =
              let uu____2878 = type_of ea  in as_iarg uu____2878  in
            [uu____2873]  in
          lid_as_constr FStar_Parser_Const.none_lid
            [FStar_Syntax_Syntax.U_zero] uu____2872
      | FStar_Pervasives_Native.Some x ->
          let uu____2888 =
            let uu____2889 =
              let uu____2894 = type_of ea  in as_iarg uu____2894  in
            let uu____2895 =
              let uu____2902 =
                let uu____2907 = embed ea x  in as_arg uu____2907  in
              [uu____2902]  in
            uu____2889 :: uu____2895  in
          lid_as_constr FStar_Parser_Const.some_lid
            [FStar_Syntax_Syntax.U_zero] uu____2888
       in
    let un trm =
      match trm with
      | Construct (fvar1,us,args) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.none_lid ->
          FStar_Pervasives_Native.Some FStar_Pervasives_Native.None
      | Construct (fvar1,us,uu____2957::(a,uu____2959)::[]) when
          FStar_Syntax_Syntax.fv_eq_lid fvar1 FStar_Parser_Const.some_lid ->
          let uu____2986 = unembed ea a  in
          FStar_Util.bind_opt uu____2986
            (fun a1  ->
               FStar_Pervasives_Native.Some (FStar_Pervasives_Native.Some a1))
      | uu____2995 -> FStar_Pervasives_Native.None  in
    let uu____2998 =
      let uu____2999 =
        let uu____3000 = let uu____3005 = type_of ea  in as_arg uu____3005
           in
        [uu____3000]  in
      lid_as_typ FStar_Parser_Const.option_lid [FStar_Syntax_Syntax.U_zero]
        uu____2999
       in
    mk_emb em un uu____2998
  
let e_tuple2 :
  'a 'b .
    'a embedding ->
      'b embedding -> ('a,'b) FStar_Pervasives_Native.tuple2 embedding
  =
  fun ea  ->
    fun eb  ->
      let em x =
        let uu____3064 =
          let uu____3065 = let uu____3070 = type_of ea  in as_iarg uu____3070
             in
          let uu____3071 =
            let uu____3078 =
              let uu____3083 = type_of eb  in as_iarg uu____3083  in
            let uu____3084 =
              let uu____3091 =
                let uu____3096 = embed ea (FStar_Pervasives_Native.fst x)  in
                as_arg uu____3096  in
              let uu____3097 =
                let uu____3104 =
                  let uu____3109 = embed eb (FStar_Pervasives_Native.snd x)
                     in
                  as_arg uu____3109  in
                [uu____3104]  in
              uu____3091 :: uu____3097  in
            uu____3078 :: uu____3084  in
          uu____3065 :: uu____3071  in
        lid_as_constr FStar_Parser_Const.lid_Mktuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____3064
         in
      let un trm =
        match trm with
        | Construct
            (fvar1,us,uu____3150::uu____3151::(a,uu____3153)::(b,uu____3155)::[])
            when
            FStar_Syntax_Syntax.fv_eq_lid fvar1
              FStar_Parser_Const.lid_Mktuple2
            ->
            let uu____3194 = unembed ea a  in
            FStar_Util.bind_opt uu____3194
              (fun a1  ->
                 let uu____3204 = unembed eb b  in
                 FStar_Util.bind_opt uu____3204
                   (fun b1  -> FStar_Pervasives_Native.Some (a1, b1)))
        | uu____3217 -> FStar_Pervasives_Native.None  in
      let uu____3222 =
        let uu____3223 =
          let uu____3224 = let uu____3229 = type_of ea  in as_arg uu____3229
             in
          let uu____3230 =
            let uu____3237 =
              let uu____3242 = type_of eb  in as_arg uu____3242  in
            [uu____3237]  in
          uu____3224 :: uu____3230  in
        lid_as_typ FStar_Parser_Const.lid_tuple2
          [FStar_Syntax_Syntax.U_zero; FStar_Syntax_Syntax.U_zero] uu____3223
         in
      mk_emb em un uu____3222
  
let (e_range : FStar_Range.range embedding) =
  let em r = Constant (Range r)  in
  let un t =
    match t with
    | Constant (Range r) -> FStar_Pervasives_Native.Some r
    | uu____3280 -> FStar_Pervasives_Native.None  in
  let uu____3281 = lid_as_typ FStar_Parser_Const.range_lid [] []  in
  mk_emb em un uu____3281 
let e_list : 'a . 'a embedding -> 'a Prims.list embedding =
  fun ea  ->
    let em l =
      let typ = let uu____3315 = type_of ea  in as_iarg uu____3315  in
      let nil =
        lid_as_constr FStar_Parser_Const.nil_lid [FStar_Syntax_Syntax.U_zero]
          [typ]
         in
      let cons1 hd1 tl1 =
        let uu____3336 =
          let uu____3337 =
            let uu____3344 =
              let uu____3349 = embed ea hd1  in as_arg uu____3349  in
            let uu____3350 = let uu____3357 = as_arg tl1  in [uu____3357]  in
            uu____3344 :: uu____3350  in
          typ :: uu____3337  in
        lid_as_constr FStar_Parser_Const.cons_lid
          [FStar_Syntax_Syntax.U_zero] uu____3336
         in
      FStar_List.fold_right cons1 l nil  in
    let rec un trm =
      match trm with
      | Construct (fv,uu____3393,uu____3394) when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nil_lid ->
          FStar_Pervasives_Native.Some []
      | Construct
          (fv,uu____3414,(uu____3415,FStar_Pervasives_Native.Some
                          (FStar_Syntax_Syntax.Implicit uu____3416))::
           (hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                 )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3445 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3445
            (fun hd2  ->
               let uu____3453 = un tl1  in
               FStar_Util.bind_opt uu____3453
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | Construct
          (fv,uu____3469,(hd1,FStar_Pervasives_Native.None )::(tl1,FStar_Pervasives_Native.None
                                                               )::[])
          when FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.cons_lid
          ->
          let uu____3494 = unembed ea hd1  in
          FStar_Util.bind_opt uu____3494
            (fun hd2  ->
               let uu____3502 = un tl1  in
               FStar_Util.bind_opt uu____3502
                 (fun tl2  -> FStar_Pervasives_Native.Some (hd2 :: tl2)))
      | uu____3517 -> FStar_Pervasives_Native.None  in
    let uu____3520 =
      let uu____3521 =
        let uu____3522 = let uu____3527 = type_of ea  in as_arg uu____3527
           in
        [uu____3522]  in
      lid_as_typ FStar_Parser_Const.list_lid [FStar_Syntax_Syntax.U_zero]
        uu____3521
       in
    mk_emb em un uu____3520
  
let e_arrow1 : 'a 'b . 'a embedding -> 'b embedding -> ('a -> 'b) embedding =
  fun ea  ->
    fun eb  ->
      let em f =
        Lam
          ((fun tas  ->
              let uu____3605 =
                let uu____3608 = FStar_List.hd tas  in unembed ea uu____3608
                 in
              match uu____3605 with
              | FStar_Pervasives_Native.Some a ->
                  let uu____3610 = f a  in embed eb uu____3610
              | FStar_Pervasives_Native.None  ->
                  failwith "cannot unembed function argument"),
            [(fun uu____3622  ->
                let uu____3625 = type_of eb  in as_arg uu____3625)],
            (Prims.parse_int "1"))
         in
      let un lam =
        match lam with
        | Lam (ft,uu____3657,uu____3658) ->
            FStar_Pervasives_Native.Some
              ((fun x  ->
                  let uu____3698 =
                    let uu____3701 =
                      let uu____3702 =
                        let uu____3705 = embed ea x  in [uu____3705]  in
                      ft uu____3702  in
                    unembed eb uu____3701  in
                  match uu____3698 with
                  | FStar_Pervasives_Native.Some x1 -> x1
                  | FStar_Pervasives_Native.None  ->
                      failwith "cannot unembed function result"))
        | uu____3707 -> FStar_Pervasives_Native.None  in
      let uu____3711 =
        let uu____3712 = type_of ea  in
        let uu____3713 = let uu____3714 = type_of eb  in as_iarg uu____3714
           in
        make_arrow1 uu____3712 uu____3713  in
      mk_emb em un uu____3711
  
let (e_norm_step : FStar_Syntax_Embeddings.norm_step embedding) =
  let em n1 =
    match n1 with
    | FStar_Syntax_Embeddings.Simpl  ->
        let uu____3726 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_simpl
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3726 [] []
    | FStar_Syntax_Embeddings.Weak  ->
        let uu____3731 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_weak
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3731 [] []
    | FStar_Syntax_Embeddings.HNF  ->
        let uu____3736 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_hnf
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3736 [] []
    | FStar_Syntax_Embeddings.Primops  ->
        let uu____3741 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_primops
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3741 [] []
    | FStar_Syntax_Embeddings.Delta  ->
        let uu____3746 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_delta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3746 [] []
    | FStar_Syntax_Embeddings.Zeta  ->
        let uu____3751 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_zeta
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3751 [] []
    | FStar_Syntax_Embeddings.Iota  ->
        let uu____3756 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_iota
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3756 [] []
    | FStar_Syntax_Embeddings.Reify  ->
        let uu____3761 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_reify
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3761 [] []
    | FStar_Syntax_Embeddings.NBE  ->
        let uu____3766 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_nbe
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        mkFV uu____3766 [] []
    | FStar_Syntax_Embeddings.UnfoldOnly l ->
        let uu____3774 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldonly
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____3775 =
          let uu____3776 =
            let uu____3781 =
              let uu____3782 = e_list e_string  in embed uu____3782 l  in
            as_arg uu____3781  in
          [uu____3776]  in
        mkFV uu____3774 [] uu____3775
    | FStar_Syntax_Embeddings.UnfoldFully l ->
        let uu____3800 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.steps_unfoldfully
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        let uu____3801 =
          let uu____3802 =
            let uu____3807 =
              let uu____3808 = e_list e_string  in embed uu____3808 l  in
            as_arg uu____3807  in
          [uu____3802]  in
        mkFV uu____3800 [] uu____3801
    | FStar_Syntax_Embeddings.UnfoldAttr a -> failwith "NBE UnfoldAttr..."
     in
  let un t0 =
    match t0 with
    | FV (fv,uu____3835,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_simpl ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Simpl
    | FV (fv,uu____3851,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_weak ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Weak
    | FV (fv,uu____3867,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_hnf ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.HNF
    | FV (fv,uu____3883,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_primops ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Primops
    | FV (fv,uu____3899,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_delta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Delta
    | FV (fv,uu____3915,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_zeta ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Zeta
    | FV (fv,uu____3931,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_iota ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Iota
    | FV (fv,uu____3947,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_nbe ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.NBE
    | FV (fv,uu____3963,[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_reify ->
        FStar_Pervasives_Native.Some FStar_Syntax_Embeddings.Reify
    | FV (fv,uu____3979,(l,uu____3981)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldonly
        ->
        let uu____4000 =
          let uu____4005 = e_list e_string  in unembed uu____4005 l  in
        FStar_Util.bind_opt uu____4000
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_16  -> FStar_Pervasives_Native.Some _0_16)
               (FStar_Syntax_Embeddings.UnfoldOnly ss))
    | FV (fv,uu____4021,(l,uu____4023)::[]) when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.steps_unfoldfully
        ->
        let uu____4042 =
          let uu____4047 = e_list e_string  in unembed uu____4047 l  in
        FStar_Util.bind_opt uu____4042
          (fun ss  ->
             FStar_All.pipe_left
               (fun _0_17  -> FStar_Pervasives_Native.Some _0_17)
               (FStar_Syntax_Embeddings.UnfoldFully ss))
    | uu____4062 ->
        ((let uu____4064 =
            let uu____4069 =
              let uu____4070 = t_to_string t0  in
              FStar_Util.format1 "Not an embedded norm_step: %s" uu____4070
               in
            (FStar_Errors.Warning_NotEmbedded, uu____4069)  in
          FStar_Errors.log_issue FStar_Range.dummyRange uu____4064);
         FStar_Pervasives_Native.None)
     in
  let uu____4071 =
    let uu____4072 =
      FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.norm_step_lid
        FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
       in
    mkFV uu____4072 [] []  in
  mk_emb em un uu____4071 
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
      let uu____4141 = let uu____4150 = e_list e  in unembed uu____4150  in
      FStar_All.pipe_right (FStar_Pervasives_Native.fst a) uu____4141
  
let (arg_as_bounded_int :
  arg ->
    (FStar_Syntax_Syntax.fv,FStar_BigInt.t) FStar_Pervasives_Native.tuple2
      FStar_Pervasives_Native.option)
  =
  fun uu____4171  ->
    match uu____4171 with
    | (a,uu____4179) ->
        (match a with
         | FV (fv1,[],(Constant (Int i),uu____4194)::[]) when
             let uu____4211 =
               FStar_Ident.text_of_lid
                 (fv1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.ends_with uu____4211 "int_to_t" ->
             FStar_Pervasives_Native.Some (fv1, i)
         | uu____4216 -> FStar_Pervasives_Native.None)
  
let (int_as_bounded : FStar_Syntax_Syntax.fv -> FStar_BigInt.t -> t) =
  fun int_to_t1  ->
    fun n1  ->
      let c = embed e_int n1  in
      let int_to_t2 args = FV (int_to_t1, [], args)  in
      let uu____4258 = let uu____4265 = as_arg c  in [uu____4265]  in
      int_to_t2 uu____4258
  
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
          let uu____4318 = f a  in FStar_Pervasives_Native.Some uu____4318
      | uu____4319 -> FStar_Pervasives_Native.None
  
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
          let uu____4372 = f a0 a1  in
          FStar_Pervasives_Native.Some uu____4372
      | uu____4373 -> FStar_Pervasives_Native.None
  
let unary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____4416 = FStar_List.map as_a args  in lift_unary f uu____4416
  
let binary_op :
  'a .
    (arg -> 'a FStar_Pervasives_Native.option) ->
      ('a -> 'a -> t) -> args -> t FStar_Pervasives_Native.option
  =
  fun as_a  ->
    fun f  ->
      fun args  ->
        let uu____4470 = FStar_List.map as_a args  in
        lift_binary f uu____4470
  
let (unary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    unary_op arg_as_int
      (fun x  -> let uu____4499 = f x  in embed e_int uu____4499)
  
let (binary_int_op :
  (FStar_BigInt.t -> FStar_BigInt.t -> FStar_BigInt.t) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_int
      (fun x  -> fun y  -> let uu____4525 = f x y  in embed e_int uu____4525)
  
let (unary_bool_op :
  (Prims.bool -> Prims.bool) -> args -> t FStar_Pervasives_Native.option) =
  fun f  ->
    unary_op arg_as_bool
      (fun x  -> let uu____4544 = f x  in embed e_bool uu____4544)
  
let (binary_bool_op :
  (Prims.bool -> Prims.bool -> Prims.bool) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_bool
      (fun x  -> fun y  -> let uu____4570 = f x y  in embed e_bool uu____4570)
  
let (binary_string_op :
  (Prims.string -> Prims.string -> Prims.string) ->
    args -> t FStar_Pervasives_Native.option)
  =
  fun f  ->
    binary_op arg_as_string
      (fun x  ->
         fun y  -> let uu____4596 = f x y  in embed e_string uu____4596)
  
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
                let uu____4698 =
                  let uu____4707 = as_a a  in
                  let uu____4710 = as_b b  in (uu____4707, uu____4710)  in
                (match uu____4698 with
                 | (FStar_Pervasives_Native.Some
                    a1,FStar_Pervasives_Native.Some b1) ->
                     let uu____4725 =
                       let uu____4726 = f a1 b1  in embed_c uu____4726  in
                     FStar_Pervasives_Native.Some uu____4725
                 | uu____4727 -> FStar_Pervasives_Native.None)
            | uu____4736 -> FStar_Pervasives_Native.None
  
let (list_of_string' : Prims.string -> t) =
  fun s  ->
    let uu____4742 = e_list e_char  in
    let uu____4749 = FStar_String.list_of_string s  in
    embed uu____4742 uu____4749
  
let (string_of_list' : FStar_Char.char Prims.list -> t) =
  fun l  ->
    let s = FStar_String.string_of_list l  in
    Constant (String (s, FStar_Range.dummyRange))
  
let (string_compare' : Prims.string -> Prims.string -> t) =
  fun s1  ->
    fun s2  ->
      let r = FStar_String.compare s1 s2  in
      let uu____4779 =
        let uu____4780 = FStar_Util.string_of_int r  in
        FStar_BigInt.big_int_of_string uu____4780  in
      embed e_int uu____4779
  
let (string_concat' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____4812 = arg_as_string a1  in
        (match uu____4812 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____4818 = arg_as_list e_string a2  in
             (match uu____4818 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.concat s1 s2  in
                  let uu____4831 = embed e_string r  in
                  FStar_Pervasives_Native.Some uu____4831
              | uu____4832 -> FStar_Pervasives_Native.None)
         | uu____4837 -> FStar_Pervasives_Native.None)
    | uu____4840 -> FStar_Pervasives_Native.None
  
let (string_of_int : FStar_BigInt.t -> t) =
  fun i  ->
    let uu____4846 = FStar_BigInt.string_of_big_int i  in
    embed e_string uu____4846
  
let (string_of_bool : Prims.bool -> t) =
  fun b  -> embed e_string (if b then "true" else "false") 
let (decidable_eq : Prims.bool -> args -> t FStar_Pervasives_Native.option) =
  fun neg  ->
    fun args  ->
      let tru = embed e_bool true  in
      let fal = embed e_bool false  in
      match args with
      | (_univ,uu____4872)::(_typ,uu____4874)::(a1,uu____4876)::(a2,uu____4878)::[]
          ->
          let uu____4899 = eq_t a1 a2  in
          (match uu____4899 with
           | FStar_Syntax_Util.Equal  ->
               FStar_Pervasives_Native.Some (if neg then fal else tru)
           | FStar_Syntax_Util.NotEqual  ->
               FStar_Pervasives_Native.Some (if neg then tru else fal)
           | uu____4904 -> FStar_Pervasives_Native.None)
      | uu____4905 -> failwith "Unexpected number of arguments"
  
let (interp_prop : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (_u,uu____4918)::(_typ,uu____4920)::(a1,uu____4922)::(a2,uu____4924)::[]
        ->
        let uu____4945 = eq_t a1 a2  in
        (match uu____4945 with
         | FStar_Syntax_Util.Equal  ->
             let uu____4948 = embed e_bool true  in
             FStar_Pervasives_Native.Some uu____4948
         | FStar_Syntax_Util.NotEqual  ->
             let uu____4949 = embed e_bool false  in
             FStar_Pervasives_Native.Some uu____4949
         | FStar_Syntax_Util.Unknown  -> FStar_Pervasives_Native.None)
    | uu____4950 -> failwith "Unexpected number of arguments"
  
let (dummy_interp :
  FStar_Ident.lid -> args -> t FStar_Pervasives_Native.option) =
  fun lid  ->
    fun args  ->
      let uu____4967 =
        let uu____4968 = FStar_Ident.string_of_lid lid  in
        Prims.strcat "No interpretation for " uu____4968  in
      failwith uu____4967
  
let (prims_to_fstar_range_step : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | (a1,uu____4981)::[] ->
        let uu____4990 = unembed e_range a1  in
        (match uu____4990 with
         | FStar_Pervasives_Native.Some r ->
             let uu____4996 = embed e_range r  in
             FStar_Pervasives_Native.Some uu____4996
         | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None)
    | uu____4997 -> failwith "Unexpected number of arguments"
  
let (string_split' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::[] ->
        let uu____5031 = arg_as_list e_char a1  in
        (match uu____5031 with
         | FStar_Pervasives_Native.Some s1 ->
             let uu____5047 = arg_as_string a2  in
             (match uu____5047 with
              | FStar_Pervasives_Native.Some s2 ->
                  let r = FStar_String.split s1 s2  in
                  let uu____5056 =
                    let uu____5057 = e_list e_string  in embed uu____5057 r
                     in
                  FStar_Pervasives_Native.Some uu____5056
              | uu____5064 -> FStar_Pervasives_Native.None)
         | uu____5067 -> FStar_Pervasives_Native.None)
    | uu____5073 -> FStar_Pervasives_Native.None
  
let (string_substring' : args -> t FStar_Pervasives_Native.option) =
  fun args  ->
    match args with
    | a1::a2::a3::[] ->
        let uu____5114 =
          let uu____5127 = arg_as_string a1  in
          let uu____5130 = arg_as_int a2  in
          let uu____5133 = arg_as_int a3  in
          (uu____5127, uu____5130, uu____5133)  in
        (match uu____5114 with
         | (FStar_Pervasives_Native.Some s1,FStar_Pervasives_Native.Some
            n1,FStar_Pervasives_Native.Some n2) ->
             let n11 = FStar_BigInt.to_int_fs n1  in
             let n21 = FStar_BigInt.to_int_fs n2  in
             (try
                let r = FStar_String.substring s1 n11 n21  in
                let uu____5164 = embed e_string r  in
                FStar_Pervasives_Native.Some uu____5164
              with | uu____5170 -> FStar_Pervasives_Native.None)
         | uu____5171 -> FStar_Pervasives_Native.None)
    | uu____5184 -> FStar_Pervasives_Native.None
  